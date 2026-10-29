package main



import (
	"bytes"
	"context"
	"database/sql"
	"encoding/base64"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"math"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	_ "modernc.org/sqlite"
	"github.com/mdp/qrterminal"

	"go.mau.fi/whatsmeow"
	"go.mau.fi/whatsmeow/appstate"
	waProto "go.mau.fi/whatsmeow/binary/proto"
	"go.mau.fi/whatsmeow/proto/waCompanionReg"
	"go.mau.fi/whatsmeow/store"
	"go.mau.fi/whatsmeow/store/sqlstore"
	"go.mau.fi/whatsmeow/types"
	"go.mau.fi/whatsmeow/types/events"
	waLog "go.mau.fi/whatsmeow/util/log"
	"google.golang.org/protobuf/proto"
)

var (
	currentQRCode string
	qrLock        sync.RWMutex

	// Multi-account globals
	multiLock       sync.RWMutex
	globalContainer *sqlstore.Container
	globalLogger    waLog.Logger
	allClients      []*whatsmeow.Client
	pairingQRCodes  = make(map[int]string)
	pairingClients  = make(map[int]*whatsmeow.Client)
)

func getLoggedInClients() []*whatsmeow.Client {
	multiLock.RLock()
	defer multiLock.RUnlock()
	var list []*whatsmeow.Client
	for _, c := range allClients {
		if c != nil && c.IsLoggedIn() {
			list = append(list, c)
		}
	}
	return list
}

func startPairingAccount(accIndex int) string {
	multiLock.Lock()

	// 1. Si ya está conectado y logueado
	if accIndex <= len(allClients) && allClients[accIndex-1] != nil && allClients[accIndex-1].IsLoggedIn() {
		multiLock.Unlock()
		return ""
	}

	// 2. Si ya hay un código QR activo y el cliente sigue conectado, retornarlo de inmediato
	if existingCli, ok := pairingClients[accIndex]; ok && existingCli != nil && existingCli.IsConnected() {
		if qr, exists := pairingQRCodes[accIndex]; exists && qr != "" {
			multiLock.Unlock()
			return qr
		}
	}

	// 3. Si el cliente no existe, o está desconectado, o no tiene QR activo: reiniciar la vinculación
	if oldCli, exists := pairingClients[accIndex]; exists && oldCli != nil {
		oldCli.Disconnect()
		delete(pairingClients, accIndex)
		delete(pairingQRCodes, accIndex)
	}

	if globalContainer == nil {
		multiLock.Unlock()
		return ""
	}

	newDev := globalContainer.NewDevice()
	cli := whatsmeow.NewClient(newDev, globalLogger)
	setupClientEventHandlers(cli)
	pairingClients[accIndex] = cli
	pairingQRCodes[accIndex] = ""

	qrChan, err := cli.GetQRChannel(context.Background())
	if err != nil {
		if globalLogger != nil {
			globalLogger.Errorf("[MultiAccount] Error getting QR channel for account %d: %v", accIndex, err)
		}
		delete(pairingClients, accIndex)
		multiLock.Unlock()
		return ""
	}

	if err := cli.Connect(); err != nil {
		if globalLogger != nil {
			globalLogger.Errorf("[MultiAccount] Error connecting account %d: %v", accIndex, err)
		}
		delete(pairingClients, accIndex)
		multiLock.Unlock()
		return ""
	}

	go func(targetIdx int, targetCli *whatsmeow.Client, ch <-chan whatsmeow.QRChannelItem) {
		for evt := range ch {
			if evt.Event == "code" {
				multiLock.Lock()
				pairingQRCodes[targetIdx] = evt.Code
				multiLock.Unlock()
				if globalLogger != nil {
					globalLogger.Infof("[MultiAccount] New QR Code received for account %d", targetIdx)
				}
				fmt.Printf("\n[MultiAccount] Scan QR for Account %d:\n", targetIdx)
				qrterminal.GenerateHalfBlock(evt.Code, qrterminal.L, os.Stdout)
			} else if evt.Event == "success" {
				multiLock.Lock()
				pairingQRCodes[targetIdx] = ""
				if targetIdx <= len(allClients) {
					allClients[targetIdx-1] = targetCli
				} else {
					allClients = append(allClients, targetCli)
				}
				delete(pairingClients, targetIdx)
				multiLock.Unlock()
				if globalLogger != nil {
					globalLogger.Infof("[MultiAccount] Account %d paired successfully!", targetIdx)
				}
				go registerBridgeWithWorker()
				go backupSessionToWorker(targetCli)
				return
			} else {
				if globalLogger != nil {
					globalLogger.Infof("[MultiAccount] QR channel event for account %d: %s", targetIdx, evt.Event)
				}
			}
		}

		// Si el canal de QR se cerró (timeout o error)
		multiLock.Lock()
		delete(pairingQRCodes, targetIdx)
		delete(pairingClients, targetIdx)
		multiLock.Unlock()
		if !targetCli.IsLoggedIn() {
			targetCli.Disconnect()
		}
	}(accIndex, cli, qrChan)

	multiLock.Unlock()

	// 4. Polling de hasta 6 segundos para retornar el QR fresco tan pronto se reciba
	for i := 0; i < 30; i++ {
		time.Sleep(200 * time.Millisecond)
		multiLock.RLock()
		code, exists := pairingQRCodes[accIndex]
		multiLock.RUnlock()
		if exists && code != "" {
			return code
		}
	}

	return ""
}

func startPhonePairing(accIndex int, phone string) (string, error) {
	cleanPhone := strings.ReplaceAll(phone, "+", "")
	cleanPhone = strings.ReplaceAll(cleanPhone, " ", "")
	cleanPhone = strings.ReplaceAll(cleanPhone, "-", "")

	multiLock.Lock()
	if globalContainer == nil {
		multiLock.Unlock()
		return "", fmt.Errorf("database container not initialized")
	}

	// Limpiar cliente previo si existía
	if oldCli, exists := pairingClients[accIndex]; exists && oldCli != nil {
		oldCli.Disconnect()
		delete(pairingClients, accIndex)
		delete(pairingQRCodes, accIndex)
	}

	newDev := globalContainer.NewDevice()
	cli := whatsmeow.NewClient(newDev, globalLogger)
	setupClientEventHandlers(cli)
	pairingClients[accIndex] = cli
	pairingQRCodes[accIndex] = ""
	multiLock.Unlock()

	if !cli.IsConnected() {
		err := cli.Connect()
		if err != nil {
			return "", fmt.Errorf("failed to connect client: %v", err)
		}
	}

	time.Sleep(1500 * time.Millisecond)

	code, err := cli.PairPhone(context.Background(), cleanPhone, true, whatsmeow.PairClientChrome, "Chrome (Windows)")
	if err != nil {
		return "", fmt.Errorf("failed to pair with phone: %v", err)
	}

	// Escuchar éxito de emparejamiento en segundo plano
	go func(targetIdx int, targetCli *whatsmeow.Client) {
		for i := 0; i < 120; i++ {
			time.Sleep(2 * time.Second)
			if targetCli.IsLoggedIn() {
				multiLock.Lock()
				if targetIdx <= len(allClients) {
					allClients[targetIdx-1] = targetCli
				} else {
					allClients = append(allClients, targetCli)
				}
				delete(pairingClients, targetIdx)
				multiLock.Unlock()
				if globalLogger != nil {
					globalLogger.Infof("[MultiAccount] Phone pairing success for Account %d!", targetIdx)
				}
				go registerBridgeWithWorker()
				go backupSessionToWorker(targetCli)
				return
			}
		}
		// Timeout
		multiLock.Lock()
		delete(pairingClients, targetIdx)
		multiLock.Unlock()
		if !targetCli.IsLoggedIn() {
			targetCli.Disconnect()
		}
	}(accIndex, cli)

	return code, nil
}

func getWorkerConfig() (string, string) {
	workerURL := os.Getenv("CLOUDFLARE_WORKER_URL")
	if workerURL == "" {
		workerURL = "https://tiktok-telegram-bot.shapiamaluci853.workers.dev"
	}
	bridgeSecret := os.Getenv("BRIDGE_SECRET")
	if bridgeSecret == "" {
		bridgeSecret = "nick_tiktok_secret_2026"
	}
	return workerURL, bridgeSecret
}

func restoreSessionFromWorker() {
	workerURL, _ := getWorkerConfig()
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Get(workerURL + "/restore-session")
	if err != nil {
		fmt.Printf("[Restore] Error al conectar con Cloudflare Worker: %v\n", err)
		return
	}
	defer resp.Body.Close()

	var data struct {
		Success bool   `json:"success"`
		DB      string `json:"db"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return
	}
	if !data.Success || data.DB == "" {
		fmt.Println("[Restore] No hay sesión previa guardada en Cloudflare KV.")
		return
	}

	decoded, err := base64.StdEncoding.DecodeString(data.DB)
	if err != nil {
		fmt.Printf("[Restore] Error decodificando sesión base64: %v\n", err)
		return
	}

	_ = os.MkdirAll("store", 0755)
	err = os.WriteFile("store/whatsapp.db", decoded, 0644)
	if err != nil {
		fmt.Printf("[Restore] Error guardando store/whatsapp.db: %v\n", err)
		return
	}
	fmt.Printf("[Restore] ¡Sesión de WhatsApp restaurada exitosamente desde Cloudflare KV (%d bytes)!\n", len(decoded))
}

func backupSessionToWorker(cli *whatsmeow.Client) {
	if cli == nil || cli.Store == nil || cli.Store.ID == nil {
		fmt.Println("[Backup] No hay sesión activa/logueada, omitiendo backup a KV.")
		return
	}
	workerURL, bridgeSecret := getWorkerConfig()
	time.Sleep(2 * time.Second) // Esperar a que SQLite complete transacciones
	data, err := os.ReadFile("store/whatsapp.db")
	if err != nil || len(data) == 0 {
		return
	}

	encoded := base64.StdEncoding.EncodeToString(data)
	payload, _ := json.Marshal(map[string]string{
		"secret": bridgeSecret,
		"db":     encoded,
	})

	req, err := http.NewRequest("POST", workerURL+"/backup-session", bytes.NewBuffer(payload))
	if err != nil {
		return
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("X-Bridge-Secret", bridgeSecret)

	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err == nil {
		defer resp.Body.Close()
		fmt.Printf("[Backup] ¡Sesión de WhatsApp respaldada exitosamente en Cloudflare KV (%d bytes)!\n", len(data))
	} else {
		fmt.Printf("[Backup] Error respaldando sesión: %v\n", err)
	}
}

func registerBridgeWithWorker() {
	workerURL, bridgeSecret := getWorkerConfig()
	renderURL := os.Getenv("RENDER_EXTERNAL_URL")
	if renderURL == "" {
		renderURL = "https://whatsapp-bridge-server-0ia4.onrender.com"
	}
	payload, _ := json.Marshal(map[string]string{
		"bridge_url": renderURL,
		"secret":     bridgeSecret,
	})
	for i := 0; i < 8; i++ {
		resp, err := http.Post(workerURL+"/register-bridge", "application/json", bytes.NewBuffer(payload))
		if err == nil && resp.StatusCode == 200 {
			fmt.Printf("[Bridge] Successfully auto-registered %s with Cloudflare Worker!\n", renderURL)
			resp.Body.Close()
			break
		}
		if resp != nil {
			resp.Body.Close()
		}
		time.Sleep(3 * time.Second)
	}
}

var (
	ytDlpPathCache string
	ytDlpLock      sync.Mutex
)

func ensureYtDlp() (string, error) {
	ytDlpLock.Lock()
	defer ytDlpLock.Unlock()

	if ytDlpPathCache != "" {
		if _, err := os.Stat(ytDlpPathCache); err == nil {
			return ytDlpPathCache, nil
		}
	}

	// 1. Check if yt-dlp is in system PATH
	if p, err := exec.LookPath("yt-dlp"); err == nil {
		ytDlpPathCache = p
		return p, nil
	}

	// 2. Check in TempDir
	targetPath := filepath.Join(os.TempDir(), "yt-dlp")
	if runtime.GOOS == "windows" {
		targetPath += ".exe"
	}

	if _, err := os.Stat(targetPath); err == nil {
		ytDlpPathCache = targetPath
		return targetPath, nil
	}

	// 3. Download standalone binary
	downloadURL := "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux"
	if runtime.GOOS == "windows" {
		downloadURL = "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"
	}

	fmt.Printf("[YT-DLP] Descargando binario yt-dlp desde %s a %s...\n", downloadURL, targetPath)
	client := &http.Client{Timeout: 90 * time.Second}
	resp, err := client.Get(downloadURL)
	if err != nil {
		return "", fmt.Errorf("error descargando yt-dlp: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("error HTTP %d descargando yt-dlp", resp.StatusCode)
	}

	out, err := os.OpenFile(targetPath, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0755)
	if err != nil {
		return "", fmt.Errorf("error creando archivo yt-dlp: %w", err)
	}
	defer out.Close()

	if _, err := io.Copy(out, resp.Body); err != nil {
		return "", fmt.Errorf("error guardando yt-dlp: %w", err)
	}

	if runtime.GOOS != "windows" {
		os.Chmod(targetPath, 0755)
	}

	fmt.Printf("[YT-DLP] Binario listo en: %s\n", targetPath)
	ytDlpPathCache = targetPath
	return targetPath, nil
}

// Message represents a chat message for our client
type Message struct {

	Time      time.Time

	Sender    string

	Content   string

	IsFromMe  bool

	MediaType string

	Filename  string

}



// Database handler for storing message history

type MessageStore struct {

	db *sql.DB

}



// Initialize message store

func NewMessageStore() (*MessageStore, error) {

	// Create directory for database if it doesn't exist

	if err := os.MkdirAll("store", 0755); err != nil {

		return nil, fmt.Errorf("failed to create store directory: %v", err)

	}



	// Open SQLite database for messages

	db, err := sql.Open("sqlite", "file:store/messages.db?_pragma=foreign_keys(1)&_pragma=journal_mode(WAL)&_pragma=busy_timeout(10000)")

	if err != nil {

		return nil, fmt.Errorf("failed to open message database: %v", err)

	}



	// Create tables if they don't exist

	_, err = db.Exec(`

		CREATE TABLE IF NOT EXISTS chats (

			jid TEXT PRIMARY KEY,

			name TEXT,

			last_message_time TIMESTAMP

		);

		

		CREATE TABLE IF NOT EXISTS messages (

			id TEXT,

			chat_jid TEXT,

			sender TEXT,

			content TEXT,

			timestamp TIMESTAMP,

			is_from_me BOOLEAN,

			media_type TEXT,

			filename TEXT,

			url TEXT,

			media_key BLOB,

			file_sha256 BLOB,

			file_enc_sha256 BLOB,

			file_length INTEGER,

			PRIMARY KEY (id, chat_jid),

			FOREIGN KEY (chat_jid) REFERENCES chats(jid)

		);

	`)

	if err != nil {

		db.Close()

		return nil, fmt.Errorf("failed to create tables: %v", err)

	}



	return &MessageStore{db: db}, nil

}



// Close the database connection

func (store *MessageStore) Close() error {

	return store.db.Close()

}



// Store a chat in the database

func (store *MessageStore) StoreChat(jid, name string, lastMessageTime time.Time) error {

	_, err := store.db.Exec(

		"INSERT OR REPLACE INTO chats (jid, name, last_message_time) VALUES (?, ?, ?)",

		jid, name, lastMessageTime,

	)

	return err

}



// Store a message in the database

func (store *MessageStore) StoreMessage(id, chatJID, sender, content string, timestamp time.Time, isFromMe bool,

	mediaType, filename, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {

	// Only store if there's actual content or media

	if content == "" && mediaType == "" {

		return nil

	}



	_, err := store.db.Exec(

		`INSERT OR REPLACE INTO messages 

		(id, chat_jid, sender, content, timestamp, is_from_me, media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length) 

		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)`,

		id, chatJID, sender, content, timestamp, isFromMe, mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength,

	)

	return err

}



// Get messages from a chat

func (store *MessageStore) GetMessages(chatJID string, limit int) ([]Message, error) {

	rows, err := store.db.Query(

		"SELECT sender, content, timestamp, is_from_me, media_type, filename FROM messages WHERE chat_jid = ? ORDER BY timestamp DESC LIMIT ?",

		chatJID, limit,

	)

	if err != nil {

		return nil, err

	}

	defer rows.Close()



	var messages []Message

	for rows.Next() {

		var msg Message

		var timestamp time.Time

		err := rows.Scan(&msg.Sender, &msg.Content, &timestamp, &msg.IsFromMe, &msg.MediaType, &msg.Filename)

		if err != nil {

			return nil, err

		}

		msg.Time = timestamp

		messages = append(messages, msg)

	}



	return messages, nil

}



// Get all chats

func (store *MessageStore) GetChats() (map[string]time.Time, error) {

	rows, err := store.db.Query("SELECT jid, last_message_time FROM chats ORDER BY last_message_time DESC")

	if err != nil {

		return nil, err

	}

	defer rows.Close()



	chats := make(map[string]time.Time)

	for rows.Next() {

		var jid string

		var lastMessageTime time.Time

		err := rows.Scan(&jid, &lastMessageTime)

		if err != nil {

			return nil, err

		}

		chats[jid] = lastMessageTime

	}



	return chats, nil

}



// Extract text content from a message

func extractTextContent(msg *waProto.Message) string {

	if msg == nil {

		return ""

	}



	// Try to get text content

	if text := msg.GetConversation(); text != "" {

		return text

	} else if extendedText := msg.GetExtendedTextMessage(); extendedText != nil {

		return extendedText.GetText()

	}



	// For now, we're ignoring non-text messages

	return ""

}



// SendMessageResponse represents the response for the send message API

type SendMessageResponse struct {

	Success bool   `json:"success"`

	Message string `json:"message"`

}



// SendMessageRequest represents the request body for the send message API

type SendMessageRequest struct {

	Recipient string   `json:"recipient"`

	Message   string   `json:"message"`

	MediaPath string   `json:"media_path,omitempty"`

	Mentions  []string `json:"mentions,omitempty"`

}



// sanitizeContactsForStatusPrivacy enforces strict exclusion of all contacts configured in WhatsApp
// privacy settings ("Mis contactos excepto..."). It reads the blacklist directly from WhatsApp,
// handles both LIDs and Phone Numbers, cross-references whatsmeow_lid_map, and deletes excluded contacts
// from SQLite and memory cache so whatsmeow's internal broadcast loop strictly drops them.
func sanitizeContactsForStatusPrivacy(c *whatsmeow.Client) (int, error) {
	if c == nil || c.Store == nil || c.Store.ID == nil {
		return 0, fmt.Errorf("client not connected")
	}
	ctx := context.Background()
	ownPhone := c.Store.ID.ToNonAD().User

	// 1. Fetch live Status Privacy settings from WhatsApp server
	privOptions, err := c.GetStatusPrivacy(ctx)
	if err != nil {
		fmt.Printf("[StatusPrivacy] Warning: could not fetch status privacy for %s: %v\n", ownPhone, err)
		return 0, err
	}

	// 2. Extract blacklisted identifiers (both LIDs and Phone Numbers)
	blacklistedIDs := make(map[string]bool)
	hasBlacklist := false
	for _, opt := range privOptions {
		if opt.Type == types.StatusPrivacyTypeBlacklist {
			hasBlacklist = true
			for _, j := range opt.List {
				u := strings.TrimSpace(j.User)
				if u != "" {
					blacklistedIDs[u] = true
				}
				// If it is an LID, resolve its Phone Number
				if j.Server == types.HiddenUserServer || j.Server == "lid" {
					if c.Store != nil && c.Store.LIDs != nil {
						if pn, err := c.Store.LIDs.GetPNForLID(ctx, j); err == nil && !pn.IsEmpty() {
							blacklistedIDs[pn.User] = true
							fmt.Printf("[StatusPrivacy] Resolved LID %s -> PN %s\n", u, pn.User)
						}
					}
				} else {
					// If it is a PN, resolve its LID
					if c.Store != nil && c.Store.LIDs != nil {
						if lid, err := c.Store.LIDs.GetLIDForPN(ctx, j); err == nil && !lid.IsEmpty() {
							blacklistedIDs[lid.User] = true
							fmt.Printf("[StatusPrivacy] Resolved PN %s -> LID %s\n", u, lid.User)
						}
					}
				}
			}
		}
	}

	if !hasBlacklist || len(blacklistedIDs) == 0 {
		fmt.Printf("[StatusPrivacy] Acc %s: No blacklist active (privacy: %v)\n", ownPhone, privOptions)
		return 0, nil
	}

	fmt.Printf("[StatusPrivacy] Acc %s: Found %d excluded identifiers in WhatsApp blacklist!\n", ownPhone, len(blacklistedIDs))

	// 3. Open SQLite to sanitize and protect contacts
	db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
	if err != nil {
		return 0, fmt.Errorf("failed to open db: %w", err)
	}
	defer db.Close()

	// Cross-reference with whatsmeow_lid_map in SQLite
	for id := range blacklistedIDs {
		var mappedPN string
		_ = db.QueryRow("SELECT pn FROM whatsmeow_lid_map WHERE lid = ?", id).Scan(&mappedPN)
		if mappedPN != "" {
			blacklistedIDs[mappedPN] = true
		}
		var mappedLID string
		_ = db.QueryRow("SELECT lid FROM whatsmeow_lid_map WHERE pn = ?", id).Scan(&mappedLID)
		if mappedLID != "" {
			blacklistedIDs[mappedLID] = true
		}
	}

	// 4. Query all contacts for this account
	rows, err := db.Query("SELECT their_jid, full_name, push_name FROM whatsmeow_contacts WHERE our_jid LIKE ?", ownPhone+"%")
	if err != nil {
		return 0, fmt.Errorf("failed to query contacts: %w", err)
	}
	defer rows.Close()

	type contactRecord struct {
		theirJID string
		fullName string
		pushName string
	}
	var toSanitize []string
	var toActivate []contactRecord

	for rows.Next() {
		var jidStr, fn, pn string
		if err := rows.Scan(&jidStr, &fn, &pn); err != nil {
			continue
		}
		parsedJID, _ := types.ParseJID(jidStr)
		contactUser := parsedJID.User
		if contactUser == "" && strings.Contains(jidStr, "@") {
			contactUser = strings.Split(jidStr, "@")[0]
		}

		isExcluded := blacklistedIDs[contactUser]
		if !isExcluded && c.Store != nil && c.Store.LIDs != nil {
			if parsedJID.Server == types.HiddenUserServer || parsedJID.Server == "lid" {
				if mappedPN, err := c.Store.LIDs.GetPNForLID(ctx, parsedJID); err == nil && !mappedPN.IsEmpty() {
					isExcluded = blacklistedIDs[mappedPN.User]
				}
			} else {
				if mappedLID, err := c.Store.LIDs.GetLIDForPN(ctx, parsedJID); err == nil && !mappedLID.IsEmpty() {
					isExcluded = blacklistedIDs[mappedLID.User]
				}
			}
		}

		if isExcluded {
			toSanitize = append(toSanitize, jidStr)
		} else {
			if fn == "" && (pn != "" || contactUser != "") {
				toActivate = append(toActivate, contactRecord{theirJID: jidStr, fullName: pn, pushName: pn})
			}
		}
	}

	sanitizedCount := 0
	for _, jidStr := range toSanitize {
		// Delete entirely from SQLite to guarantee whatsmeow cannot see it
		_, _ = db.Exec("DELETE FROM whatsmeow_contacts WHERE our_jid LIKE ? AND their_jid = ?", ownPhone+"%", jidStr)
		parsedJID, _ := types.ParseJID(jidStr)
		_ = c.Store.Contacts.PutContactName(ctx, parsedJID, "", "")
		sanitizedCount++
		fmt.Printf("[StatusPrivacy] Acc %s: 🚫 EXCLUDED contact deleted & purged: %s\n", ownPhone, jidStr)
	}

	// Guarantee every blacklisted identifier has full_name = '' in cache for all servers
	for blID := range blacklistedIDs {
		for _, srv := range []string{"s.whatsapp.net", "c.us", "lid"} {
			blJID := types.JID{User: blID, Server: srv}
			_ = c.Store.Contacts.PutContactName(ctx, blJID, "", "")
		}
	}

	// For non-blacklisted contacts, activate them so they receive the status broadcast
	for _, rec := range toActivate {
		displayName := rec.pushName
		if displayName == "" {
			displayName = "Contact"
		}
		_, _ = db.Exec("UPDATE whatsmeow_contacts SET full_name = ? WHERE our_jid LIKE ? AND their_jid = ?", displayName, ownPhone+"%", rec.theirJID)
		parsedJID, _ := types.ParseJID(rec.theirJID)
		_ = c.Store.Contacts.PutContactName(ctx, parsedJID, displayName, "")
	}

	fmt.Printf("[StatusPrivacy] Acc %s: Privacy strictly enforced! %d excluded contacts purged, %d allowed contacts activated.\n",
		ownPhone, sanitizedCount, len(toActivate))
	return sanitizedCount, nil
}

// Function to send a WhatsApp message

func sendWhatsAppMessage(client *whatsmeow.Client, recipient string, message string, mediaPath string, mentions []string) (bool, string) {

	if !client.IsConnected() {

		fmt.Println("[Bridge] Client not connected, attempting auto-reconnect...")

		_ = client.Connect()

		for i := 0; i < 10; i++ {

			if client.IsConnected() {

				fmt.Println("[Bridge] Successfully reconnected to WhatsApp!")

				break

			}

			time.Sleep(500 * time.Millisecond)

		}

		if !client.IsConnected() {

			return false, "Not connected to WhatsApp"

		}

	}



	// Create JID for recipient

	var recipientJID types.JID

	var err error



	// Check if recipient is status broadcast

	if recipient == "status" || recipient == "status@broadcast" {

		recipientJID = types.JID{

			User:   "status",

			Server: "broadcast",

		}

		// Strictly sanitize and enforce WhatsApp privacy rules before sending to status@broadcast
		if _, sanitizeErr := sanitizeContactsForStatusPrivacy(client); sanitizeErr != nil {
			fmt.Printf("[StatusPrivacy] Warning: sanitize failed: %v\n", sanitizeErr)
		}

	} else if strings.Contains(recipient, "@") {

		// Parse the JID string

		recipientJID, err = types.ParseJID(recipient)

		if err != nil {

			return false, fmt.Sprintf("Error parsing JID: %v", err)

		}

	} else {

		// Create JID from phone number

		recipientJID = types.JID{

			User:   recipient,

			Server: "s.whatsapp.net", // For personal chats

		}

	}



	var ctxInfo *waProto.ContextInfo

	if len(mentions) > 0 {

		ctxInfo = &waProto.ContextInfo{

			MentionedJID: mentions,

		}

	}



	msg := &waProto.Message{}



	// Check if we have media to send

	if mediaPath != "" {

		// Read media file or download from URL
		var mediaData []byte
		var fileExt string
		if strings.HasPrefix(mediaPath, "http://") || strings.HasPrefix(mediaPath, "https://") {
			fmt.Printf("[Bridge] Downloading media from URL: %s\n", mediaPath)
			httpReq, err := http.NewRequestWithContext(context.Background(), "GET", mediaPath, nil)
			if err != nil {
				return false, fmt.Sprintf("Error creating download request: %v", err)
			}
			httpReq.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
			httpReq.Header.Set("Referer", "https://www.tiktok.com/")
			httpReq.Header.Set("Accept", "*/*")

			httpClient := &http.Client{Timeout: 90 * time.Second}
			resp, err := httpClient.Do(httpReq)
			if err != nil {
				return false, fmt.Sprintf("Error downloading media from URL: %v", err)
			}
			defer resp.Body.Close()

			if resp.StatusCode != http.StatusOK {
				return false, fmt.Sprintf("Error downloading media: HTTP %d %s", resp.StatusCode, resp.Status)
			}

			mediaData, err = io.ReadAll(resp.Body)
			if err != nil {
				return false, fmt.Sprintf("Error reading downloaded media: %v", err)
			}

			if len(mediaData) < 1024 {
				return false, fmt.Sprintf("Downloaded media is too small (%d bytes), invalid file", len(mediaData))
			}

			// Detect type from Content-Type header first
			cType := strings.ToLower(resp.Header.Get("Content-Type"))
			if strings.Contains(cType, "video") {
				fileExt = "mp4"
			} else if strings.Contains(cType, "image") {
				if strings.Contains(cType, "png") {
					fileExt = "png"
				} else if strings.Contains(cType, "webp") {
					fileExt = "webp"
				} else {
					fileExt = "jpg"
				}
			} else {
				cleanPath := mediaPath
				if u, err := url.Parse(mediaPath); err == nil && u.Path != "" {
					cleanPath = u.Path
				}
				fileExt = strings.ToLower(filepath.Ext(cleanPath))
				fileExt = strings.TrimPrefix(fileExt, ".")
				if fileExt == "" {
					fileExt = "mp4"
				}
			}
		} else {
			var err error
			mediaData, err = os.ReadFile(mediaPath)
			if err != nil {
				return false, fmt.Sprintf("Error reading media file: %v", err)
			}
			fileExt = strings.ToLower(mediaPath[strings.LastIndex(mediaPath, ".")+1:])
		}

		var mediaType whatsmeow.MediaType
		var mimeType string

		switch fileExt {

		// Image types

		case "jpg", "jpeg":

			mediaType = whatsmeow.MediaImage

			mimeType = "image/jpeg"

		case "png":

			mediaType = whatsmeow.MediaImage

			mimeType = "image/png"

		case "gif":

			mediaType = whatsmeow.MediaImage

			mimeType = "image/gif"

		case "webp":

			mediaType = whatsmeow.MediaImage

			mimeType = "image/webp"



		// Audio types

		case "ogg":

			mediaType = whatsmeow.MediaAudio

			mimeType = "audio/ogg; codecs=opus"



		// Video types

		case "mp4":

			mediaType = whatsmeow.MediaVideo

			mimeType = "video/mp4"

		case "avi":

			mediaType = whatsmeow.MediaVideo

			mimeType = "video/avi"

		case "mov":

			mediaType = whatsmeow.MediaVideo

			mimeType = "video/quicktime"



		// Document types

		case "xlsx":

			mediaType = whatsmeow.MediaDocument

			mimeType = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"

		case "xls":

			mediaType = whatsmeow.MediaDocument

			mimeType = "application/vnd.ms-excel"

		case "pdf":

			mediaType = whatsmeow.MediaDocument

			mimeType = "application/pdf"

		default:

			mediaType = whatsmeow.MediaDocument

			mimeType = "application/octet-stream"

		}



		// Upload media to WhatsApp servers

		resp, err := client.Upload(context.Background(), mediaData, mediaType)

		if err != nil {

			return false, fmt.Sprintf("Error uploading media: %v", err)

		}



		fmt.Println("Media uploaded", resp)



		// Create the appropriate message type based on media type
		var captionPtr *string
		if strings.TrimSpace(message) != "" {
			c := strings.TrimSpace(message)
			captionPtr = &c
		}

		switch mediaType {

		case whatsmeow.MediaImage:

			msg.ImageMessage = &waProto.ImageMessage{

				Caption:       captionPtr,

				Mimetype:      proto.String(mimeType),

				URL:           &resp.URL,

				DirectPath:    &resp.DirectPath,

				MediaKey:      resp.MediaKey,

				FileEncSHA256: resp.FileEncSHA256,

				FileSHA256:    resp.FileSHA256,

				FileLength:    &resp.FileLength,

				ContextInfo:   ctxInfo,

			}

		case whatsmeow.MediaAudio:

			// Handle ogg audio files

			var seconds uint32 = 30 // Default fallback

			var waveform []byte = nil



			// Try to analyze the ogg file

			if strings.Contains(mimeType, "ogg") {

				analyzedSeconds, analyzedWaveform, err := analyzeOggOpus(mediaData)

				if err == nil {

					seconds = analyzedSeconds

					waveform = analyzedWaveform

				} else {

					return false, fmt.Sprintf("Failed to analyze Ogg Opus file: %v", err)

				}

			} else {

				fmt.Printf("Not an Ogg Opus file: %s\n", mimeType)

			}



			msg.AudioMessage = &waProto.AudioMessage{

				Mimetype:      proto.String(mimeType),

				URL:           &resp.URL,

				DirectPath:    &resp.DirectPath,

				MediaKey:      resp.MediaKey,

				FileEncSHA256: resp.FileEncSHA256,

				FileSHA256:    resp.FileSHA256,

				FileLength:    &resp.FileLength,

				Seconds:       proto.Uint32(seconds),

				PTT:           proto.Bool(true),

				Waveform:      waveform,

			}

		case whatsmeow.MediaVideo:

			msg.VideoMessage = &waProto.VideoMessage{

				Caption:       captionPtr,

				Mimetype:      proto.String(mimeType),

				URL:           &resp.URL,

				DirectPath:    &resp.DirectPath,

				MediaKey:      resp.MediaKey,

				FileEncSHA256: resp.FileEncSHA256,

				FileSHA256:    resp.FileSHA256,

				FileLength:    &resp.FileLength,

				ContextInfo:   ctxInfo,

			}

		case whatsmeow.MediaDocument:

			baseName := filepath.Base(mediaPath)

			msg.DocumentMessage = &waProto.DocumentMessage{

				Title:         proto.String(baseName),

				FileName:      proto.String(baseName),

				Caption:       captionPtr,

				Mimetype:      proto.String(mimeType),

				URL:           &resp.URL,

				DirectPath:    &resp.DirectPath,

				MediaKey:      resp.MediaKey,

				FileEncSHA256: resp.FileEncSHA256,

				FileSHA256:    resp.FileSHA256,

				FileLength:    &resp.FileLength,

			}

		}

	} else {

		if ctxInfo != nil || recipientJID.Server == "broadcast" {

			msg.ExtendedTextMessage = &waProto.ExtendedTextMessage{

				Text:        proto.String(message),

				ContextInfo: ctxInfo,

			}

		} else {

			msg.Conversation = proto.String(message)

		}

	}



	// Send message

	respSend, err := client.SendMessage(context.Background(), recipientJID, msg)

	if err != nil {

		return false, fmt.Sprintf("Error sending message: %v", err)

	}

	// Record status post for analytics & views tracking
	if recipientJID.Server == "broadcast" {
		ownPhone := ""
		if client.Store != nil && client.Store.ID != nil {
			ownPhone = client.Store.ID.ToNonAD().User
		}
		mediaType := "text"
		if msg.GetImageMessage() != nil {
			mediaType = "image"
		} else if msg.GetVideoMessage() != nil {
			mediaType = "video"
		}
		recordStatusPost(string(respSend.ID), ownPhone, message, mediaType, respSend.Timestamp)
	}

	return true, fmt.Sprintf("Message sent to %s", recipient)

}

// Status Tracker DB & Event Handlers
func initStatusTrackerDB() error {
	db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
	if err != nil {
		return err
	}
	defer db.Close()

	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS status_posts (
			id TEXT PRIMARY KEY,
			account_phone TEXT,
			caption TEXT,
			media_type TEXT,
			created_at DATETIME
		);
		CREATE TABLE IF NOT EXISTS status_views (
			id INTEGER PRIMARY KEY AUTOINCREMENT,
			status_id TEXT,
			account_phone TEXT,
			viewer_jid TEXT,
			viewer_phone TEXT,
			viewer_name TEXT,
			viewed_at DATETIME,
			UNIQUE(status_id, viewer_phone)
		);
		CREATE INDEX IF NOT EXISTS idx_status_views_status_id ON status_views(status_id);
		CREATE INDEX IF NOT EXISTS idx_status_posts_acc ON status_posts(account_phone);
	`)
	if err == nil {
		fmt.Println("[StatusTracker] Initialized SQLite tables (status_posts, status_views)")
	}
	return err
}

func recordStatusPost(id, accountPhone, caption, mediaType string, createdAt time.Time) {
	if id == "" {
		return
	}
	db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
	if err != nil {
		return
	}
	defer db.Close()
	if createdAt.IsZero() {
		createdAt = time.Now()
	}
	_, _ = db.Exec(`
		INSERT INTO status_posts (id, account_phone, caption, media_type, created_at)
		VALUES (?, ?, ?, ?, ?)
		ON CONFLICT(id) DO UPDATE SET caption=excluded.caption
	`, id, accountPhone, caption, mediaType, createdAt.Format(time.RFC3339))
	fmt.Printf("[StatusTracker] 🎬 Recorded status post %s for %s (%s)\n", id, accountPhone, mediaType)
}

func recordStatusView(statusID, accountPhone, viewerJID, viewerPhone, viewerName string, viewedAt time.Time) {
	if statusID == "" || viewerPhone == "" {
		return
	}
	db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
	if err != nil {
		return
	}
	defer db.Close()
	if viewedAt.IsZero() {
		viewedAt = time.Now()
	}
	res, err := db.Exec(`
		INSERT OR IGNORE INTO status_views (status_id, account_phone, viewer_jid, viewer_phone, viewer_name, viewed_at)
		VALUES (?, ?, ?, ?, ?, ?)
	`, statusID, accountPhone, viewerJID, viewerPhone, viewerName, viewedAt.Format(time.RFC3339))
	if err == nil {
		if rows, _ := res.RowsAffected(); rows > 0 {
			fmt.Printf("[StatusTracker] 👀 New status view on %s: %s (%s)\n", statusID, viewerName, viewerPhone)
		}
	}
}

func handleReceiptEvent(c *whatsmeow.Client, evt *events.Receipt) {
	if evt == nil {
		return
	}
	isStatusReceipt := evt.Chat == types.StatusBroadcastJID || evt.Chat.User == "status" || strings.HasPrefix(evt.Chat.String(), "status@")
	if !isStatusReceipt {
		return
	}

	if evt.Type != types.ReceiptTypeRead && evt.Type != types.ReceiptTypeReadSelf {
		return
	}

	ownPhone := ""
	if c.Store != nil && c.Store.ID != nil {
		ownPhone = c.Store.ID.ToNonAD().User
	}

	viewerJID := evt.Sender
	viewerUser := viewerJID.User
	viewerName := ""

	ctx := context.Background()
	if c.Store != nil && c.Store.Contacts != nil {
		if contact, err := c.Store.Contacts.GetContact(ctx, viewerJID); err == nil && contact.Found {
			if contact.FullName != "" {
				viewerName = contact.FullName
			} else if contact.PushName != "" {
				viewerName = contact.PushName
			}
		}
	}

	if viewerJID.Server == types.HiddenUserServer || viewerJID.Server == "lid" {
		db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
		if err == nil {
			defer db.Close()
			var mappedPN string
			_ = db.QueryRow("SELECT pn FROM whatsmeow_lid_map WHERE lid = ?", viewerUser).Scan(&mappedPN)
			if mappedPN != "" {
				viewerUser = mappedPN
				pnJID := types.JID{User: mappedPN, Server: types.DefaultUserServer}
				if contact, err := c.Store.Contacts.GetContact(ctx, pnJID); err == nil && contact.Found {
					if contact.FullName != "" {
						viewerName = contact.FullName
					} else if contact.PushName != "" && viewerName == "" {
						viewerName = contact.PushName
					}
				}
			}
		}
	}

	if viewerName == "" {
		viewerName = "+" + viewerUser
	}

	ts := evt.Timestamp
	if ts.IsZero() {
		ts = time.Now()
	}

	for _, msgID := range evt.MessageIDs {
		strMsgID := string(msgID)
		if strMsgID == "" {
			continue
		}
		recordStatusView(strMsgID, ownPhone, viewerJID.String(), viewerUser, viewerName, ts)
	}
}

func handleMessageEvent(c *whatsmeow.Client, msg *events.Message) {
	if msg == nil {
		return
	}
	if msg.Info.Chat == types.StatusBroadcastJID || msg.Info.Chat.User == "status" {
		if msg.Info.IsFromMe {
			ownPhone := ""
			if c.Store != nil && c.Store.ID != nil {
				ownPhone = c.Store.ID.ToNonAD().User
			}
			caption := ""
			mediaType := "text"
			if msg.Message.GetExtendedTextMessage() != nil {
				caption = msg.Message.GetExtendedTextMessage().GetText()
			} else if msg.Message.GetConversation() != "" {
				caption = msg.Message.GetConversation()
			} else if msg.Message.GetImageMessage() != nil {
				mediaType = "image"
				caption = msg.Message.GetImageMessage().GetCaption()
			} else if msg.Message.GetVideoMessage() != nil {
				mediaType = "video"
				caption = msg.Message.GetVideoMessage().GetCaption()
			}
			ts := msg.Info.Timestamp
			if ts.IsZero() {
				ts = time.Now()
			}
			recordStatusPost(string(msg.Info.ID), ownPhone, caption, mediaType, ts)
		}
	}
}

func setupClientEventHandlers(c *whatsmeow.Client) {
	if c == nil {
		return
	}
	c.AddEventHandler(func(rawEvt any) {
		switch evt := rawEvt.(type) {
		case *events.Receipt:
			handleReceiptEvent(c, evt)
		case *events.Message:
			handleMessageEvent(c, evt)
		}
	})
}

func parseFlexibleTime(s string) time.Time {
	if s == "" {
		return time.Time{}
	}
	layouts := []string{
		time.RFC3339Nano,
		time.RFC3339,
		"2006-01-02 15:04:05 -0700 MST",
		"2006-01-02 15:04:05.999999999 -0700 MST",
		"2006-01-02 15:04:05",
		"2006-01-02T15:04:05Z07:00",
		"2006-01-02 15:04:05-07:00",
		"2006-01-02T15:04:05",
	}
	for _, layout := range layouts {
		if t, err := time.Parse(layout, s); err == nil {
			return t
		}
	}
	return time.Time{}
}

func formatTimeAgo(t time.Time) string {
	if t.IsZero() {
		return ""
	}
	diff := time.Since(t)
	if diff < time.Minute {
		return "hace unos segundos"
	} else if diff < time.Hour {
		mins := int(diff.Minutes())
		if mins <= 1 {
			return "hace 1 min"
		}
		return fmt.Sprintf("hace %d min", mins)
	} else if diff < 24*time.Hour {
		hrs := int(diff.Hours())
		mins := int(diff.Minutes()) % 60
		if hrs == 1 {
			if mins > 0 {
				return fmt.Sprintf("hace 1h %dm", mins)
			}
			return "hace 1h"
		}
		if mins > 0 {
			return fmt.Sprintf("hace %dh %dm", hrs, mins)
		}
		return fmt.Sprintf("hace %d horas", hrs)
	}
	days := int(diff.Hours() / 24)
	if days == 1 {
		return "hace 1 día"
	}
	return fmt.Sprintf("hace %d días", days)
}



// Extract media info from a message

func extractMediaInfo(msg *waProto.Message) (mediaType string, filename string, url string, mediaKey []byte, fileSHA256 []byte, fileEncSHA256 []byte, fileLength uint64) {

	if msg == nil {

		return "", "", "", nil, nil, nil, 0

	}



	// Check for image message

	if img := msg.GetImageMessage(); img != nil {

		return "image", "image_" + time.Now().Format("20060102_150405") + ".jpg",

			img.GetURL(), img.GetMediaKey(), img.GetFileSHA256(), img.GetFileEncSHA256(), img.GetFileLength()

	}



	// Check for video message

	if vid := msg.GetVideoMessage(); vid != nil {

		return "video", "video_" + time.Now().Format("20060102_150405") + ".mp4",

			vid.GetURL(), vid.GetMediaKey(), vid.GetFileSHA256(), vid.GetFileEncSHA256(), vid.GetFileLength()

	}



	// Check for audio message

	if aud := msg.GetAudioMessage(); aud != nil {

		return "audio", "audio_" + time.Now().Format("20060102_150405") + ".ogg",

			aud.GetURL(), aud.GetMediaKey(), aud.GetFileSHA256(), aud.GetFileEncSHA256(), aud.GetFileLength()

	}



	// Check for document message

	if doc := msg.GetDocumentMessage(); doc != nil {

		filename := doc.GetFileName()

		if filename == "" {

			filename = "document_" + time.Now().Format("20060102_150405")

		}

		return "document", filename,

			doc.GetURL(), doc.GetMediaKey(), doc.GetFileSHA256(), doc.GetFileEncSHA256(), doc.GetFileLength()

	}



	return "", "", "", nil, nil, nil, 0

}



// Handle regular incoming messages with media support

func handleMessage(client *whatsmeow.Client, messageStore *MessageStore, msg *events.Message, logger waLog.Logger) {

	// Save message to database

	chatJID := msg.Info.Chat.String()

	sender := msg.Info.Sender.User



	// Get appropriate chat name (pass nil for conversation since we don't have one for regular messages)

	name := GetChatName(client, messageStore, msg.Info.Chat, chatJID, nil, sender, logger)



	// Update chat in database with the message timestamp (keeps last message time updated)

	err := messageStore.StoreChat(chatJID, name, msg.Info.Timestamp)

	if err != nil {

		logger.Warnf("Failed to store chat: %v", err)

	}



	// Extract text content

	content := extractTextContent(msg.Message)



	// Extract media info

	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength := extractMediaInfo(msg.Message)



	// Skip if there's no content and no media

	if content == "" && mediaType == "" {

		return

	}



	// Store message in database

	err = messageStore.StoreMessage(

		msg.Info.ID,

		chatJID,

		sender,

		content,

		msg.Info.Timestamp,

		msg.Info.IsFromMe,

		mediaType,

		filename,

		url,

		mediaKey,

		fileSHA256,

		fileEncSHA256,

		fileLength,

	)



	if err != nil {

		logger.Warnf("Failed to store message: %v", err)

	} else {

		// Log message reception

		timestamp := msg.Info.Timestamp.Format("2006-01-02 15:04:05")

		direction := "←"

		if msg.Info.IsFromMe {

			direction = "→"

		}



		// Log based on message type

		if mediaType != "" {

			fmt.Printf("[%s] %s %s: [%s: %s] %s\n", timestamp, direction, sender, mediaType, filename, content)

		} else if content != "" {

			fmt.Printf("[%s] %s %s: %s\n", timestamp, direction, sender, content)

		}

	}

	// Auto-descargador bidireccional de redes sociales en WhatsApp
	if content != "" {
		go handleSocialLinkAutoReply(client, msg, content)
	}

}

var socialMediaRegex = regexp.MustCompile(`(?i)https?://[^\s]*(?:tiktok\.com|instagram\.com|instagr\.am|youtube\.com|youtu\.be|twitter\.com|x\.com|facebook\.com|fb\.watch)[^\s]*`)

type ScrapeResponse struct {
	Success bool `json:"success"`
	Item    struct {
		ID       string   `json:"id"`
		Platform string   `json:"platform"`
		IsImages bool     `json:"isImages"`
		Images   []string `json:"images"`
		VideoURL string   `json:"videoUrl"`
		Title    string   `json:"title"`
		Author   string   `json:"author"`
	} `json:"item"`
	Error string `json:"error"`
}

func handleSocialLinkAutoReply(client *whatsmeow.Client, msg *events.Message, content string) {
	if strings.Contains(content, "Descargado por tu Bot") || strings.Contains(content, "⏳ *Descargando") {
		return
	}
	link := socialMediaRegex.FindString(content)
	if link == "" {
		return
	}

	chatJID := msg.Info.Chat.String()
	fmt.Printf("[AutoBot] Enlace detectado en chat %s: %s\n", chatJID, link)

	// Notificar procesamiento
	sendWhatsAppMessage(client, chatJID, "⏳ *Descargando contenido...*\n_Extrayendo en máxima resolución sin marcas de agua..._", "", nil)

	workerURL, _ := getWorkerConfig()
	scrapeEndpoint := fmt.Sprintf("%s/api/scrape?url=%s", workerURL, url.QueryEscape(link))

	httpClient := &http.Client{Timeout: 45 * time.Second}
	resp, err := httpClient.Get(scrapeEndpoint)
	if err != nil {
		fmt.Printf("[AutoBot] Error llamando a scrape: %v\n", err)
		sendWhatsAppMessage(client, chatJID, "❌ Error de conexión al descargar el video.", "", nil)
		return
	}
	defer resp.Body.Close()

	var scrapeRes ScrapeResponse
	if err := json.NewDecoder(resp.Body).Decode(&scrapeRes); err != nil || !scrapeRes.Success {
		fmt.Printf("[AutoBot] Fallo al extraer contenido: %v | err: %s\n", err, scrapeRes.Error)
		sendWhatsAppMessage(client, chatJID, "⚠️ No se pudo procesar este enlace. Asegúrate de que sea público.", "", nil)
		return
	}

	caption := fmt.Sprintf("✨ *%s*\n👤 *%s*\n🤖 *Descargado por tu Bot*", scrapeRes.Item.Title, scrapeRes.Item.Author)

	if scrapeRes.Item.VideoURL != "" {
		fmt.Printf("[AutoBot] Enviando video a %s (%s)...\n", chatJID, scrapeRes.Item.VideoURL)
		ok, sendMsg := sendWhatsAppMessage(client, chatJID, caption, scrapeRes.Item.VideoURL, nil)
		if !ok {
			fmt.Printf("[AutoBot] Error enviando video: %s\n", sendMsg)
		}
	} else if scrapeRes.Item.IsImages && len(scrapeRes.Item.Images) > 0 {
		for i, imgUrl := range scrapeRes.Item.Images {
			imgCaption := ""
			if i == 0 {
				imgCaption = caption
			}
			sendWhatsAppMessage(client, chatJID, imgCaption, imgUrl, nil)
			time.Sleep(500 * time.Millisecond)
		}
	}
}



// DownloadMediaRequest represents the request body for the download media API

type DownloadMediaRequest struct {

	MessageID string `json:"message_id"`

	ChatJID   string `json:"chat_jid"`

}



// DownloadMediaResponse represents the response for the download media API

type DownloadMediaResponse struct {

	Success  bool   `json:"success"`

	Message  string `json:"message"`

	Filename string `json:"filename,omitempty"`

	Path     string `json:"path,omitempty"`

}



// Store additional media info in the database

func (store *MessageStore) StoreMediaInfo(id, chatJID, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {

	_, err := store.db.Exec(

		"UPDATE messages SET url = ?, media_key = ?, file_sha256 = ?, file_enc_sha256 = ?, file_length = ? WHERE id = ? AND chat_jid = ?",

		url, mediaKey, fileSHA256, fileEncSHA256, fileLength, id, chatJID,

	)

	return err

}



// Get media info from the database

func (store *MessageStore) GetMediaInfo(id, chatJID string) (string, string, string, []byte, []byte, []byte, uint64, error) {

	var mediaType, filename, url string

	var mediaKey, fileSHA256, fileEncSHA256 []byte

	var fileLength uint64



	err := store.db.QueryRow(

		"SELECT media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length FROM messages WHERE id = ? AND chat_jid = ?",

		id, chatJID,

	).Scan(&mediaType, &filename, &url, &mediaKey, &fileSHA256, &fileEncSHA256, &fileLength)



	return mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err

}



// MediaDownloader implements the whatsmeow.DownloadableMessage interface

type MediaDownloader struct {

	URL           string

	DirectPath    string

	MediaKey      []byte

	FileLength    uint64

	FileSHA256    []byte

	FileEncSHA256 []byte

	MediaType     whatsmeow.MediaType

}



// GetDirectPath implements the DownloadableMessage interface

func (d *MediaDownloader) GetDirectPath() string {

	return d.DirectPath

}



// GetURL implements the DownloadableMessage interface

func (d *MediaDownloader) GetURL() string {

	return d.URL

}



// GetMediaKey implements the DownloadableMessage interface

func (d *MediaDownloader) GetMediaKey() []byte {

	return d.MediaKey

}



// GetFileLength implements the DownloadableMessage interface

func (d *MediaDownloader) GetFileLength() uint64 {

	return d.FileLength

}



// GetFileSHA256 implements the DownloadableMessage interface

func (d *MediaDownloader) GetFileSHA256() []byte {

	return d.FileSHA256

}



// GetFileEncSHA256 implements the DownloadableMessage interface

func (d *MediaDownloader) GetFileEncSHA256() []byte {

	return d.FileEncSHA256

}



// GetMediaType implements the DownloadableMessage interface

func (d *MediaDownloader) GetMediaType() whatsmeow.MediaType {

	return d.MediaType

}



// Function to download media from a message

func downloadMedia(client *whatsmeow.Client, messageStore *MessageStore, messageID, chatJID string) (bool, string, string, string, error) {

	// Query the database for the message

	var mediaType, filename, url string

	var mediaKey, fileSHA256, fileEncSHA256 []byte

	var fileLength uint64

	var err error



	// First, check if we already have this file

	chatDir := fmt.Sprintf("store/%s", strings.ReplaceAll(chatJID, ":", "_"))

	localPath := ""



	// Get media info from the database

	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err = messageStore.GetMediaInfo(messageID, chatJID)



	if err != nil {

		// Try to get basic info if extended info isn't available

		err = messageStore.db.QueryRow(

			"SELECT media_type, filename FROM messages WHERE id = ? AND chat_jid = ?",

			messageID, chatJID,

		).Scan(&mediaType, &filename)



		if err != nil {

			return false, "", "", "", fmt.Errorf("failed to find message: %v", err)

		}

	}



	// Check if this is a media message

	if mediaType == "" {

		return false, "", "", "", fmt.Errorf("not a media message")

	}



	// Create directory for the chat if it doesn't exist

	if err := os.MkdirAll(chatDir, 0755); err != nil {

		return false, "", "", "", fmt.Errorf("failed to create chat directory: %v", err)

	}



	// Generate a local path for the file

	localPath = fmt.Sprintf("%s/%s", chatDir, filename)



	// Get absolute path

	absPath, err := filepath.Abs(localPath)

	if err != nil {

		return false, "", "", "", fmt.Errorf("failed to get absolute path: %v", err)

	}



	// Check if file already exists

	if _, err := os.Stat(localPath); err == nil {

		// File exists, return it

		return true, mediaType, filename, absPath, nil

	}



	// If we don't have all the media info we need, we can't download

	if url == "" || len(mediaKey) == 0 || len(fileSHA256) == 0 || len(fileEncSHA256) == 0 || fileLength == 0 {

		return false, "", "", "", fmt.Errorf("incomplete media information for download")

	}



	fmt.Printf("Attempting to download media for message %s in chat %s...\n", messageID, chatJID)



	// Extract direct path from URL

	directPath := extractDirectPathFromURL(url)



	// Create a downloader that implements DownloadableMessage

	var waMediaType whatsmeow.MediaType

	switch mediaType {

	case "image":

		waMediaType = whatsmeow.MediaImage

	case "video":

		waMediaType = whatsmeow.MediaVideo

	case "audio":

		waMediaType = whatsmeow.MediaAudio

	case "document":

		waMediaType = whatsmeow.MediaDocument

	default:

		return false, "", "", "", fmt.Errorf("unsupported media type: %s", mediaType)

	}



	downloader := &MediaDownloader{

		URL:           url,

		DirectPath:    directPath,

		MediaKey:      mediaKey,

		FileLength:    fileLength,

		FileSHA256:    fileSHA256,

		FileEncSHA256: fileEncSHA256,

		MediaType:     waMediaType,

	}



	// Download the media using whatsmeow client

	mediaData, err := client.Download(context.Background(), downloader)

	if err != nil {

		return false, "", "", "", fmt.Errorf("failed to download media: %v", err)

	}



	// Save the downloaded media to file

	if err := os.WriteFile(localPath, mediaData, 0644); err != nil {

		return false, "", "", "", fmt.Errorf("failed to save media file: %v", err)

	}



	fmt.Printf("Successfully downloaded %s media to %s (%d bytes)\n", mediaType, absPath, len(mediaData))

	return true, mediaType, filename, absPath, nil

}



// Extract direct path from a WhatsApp media URL

func extractDirectPathFromURL(url string) string {

	// The direct path is typically in the URL, we need to extract it

	// Example URL: https://mmg.whatsapp.net/v/t62.7118-24/13812002_698058036224062_3424455886509161511_n.enc?ccb=11-4&oh=...



	// Find the path part after the domain

	parts := strings.SplitN(url, ".net/", 2)

	if len(parts) < 2 {

		return url // Return original URL if parsing fails

	}



	pathPart := parts[1]



	// Remove query parameters

	pathPart = strings.SplitN(pathPart, "?", 2)[0]



	// Create proper direct path format

	return "/" + pathPart

}



// Start a REST API server to expose the WhatsApp client functionality

func startRESTServer(client *whatsmeow.Client, messageStore *MessageStore, defaultPort int) {
	port := defaultPort
	if pStr := os.Getenv("PORT"); pStr != "" {
		if p, err := strconv.Atoi(pStr); err == nil {
			port = p
		}
	}

	http.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/plain")
		w.WriteHeader(http.StatusOK)
		w.Write([]byte("OK"))
	})

	http.HandleFunc("/api/qr", func(w http.ResponseWriter, r *http.Request) {
		accStr := r.URL.Query().Get("account")
		phone := r.URL.Query().Get("phone")
		accNum := 1
		if a, err := strconv.Atoi(accStr); err == nil && a >= 1 {
			accNum = a
		}

		if accNum > 1 {
			// Si se envió un número telefónico, generar código de 8 dígitos para vincular sin cámara
			if phone != "" {
				code, err := startPhonePairing(accNum, phone)
				w.Header().Set("Content-Type", "application/json")
				if err != nil {
					json.NewEncoder(w).Encode(map[string]interface{}{
						"success": false,
						"account": accNum,
						"error":   err.Error(),
					})
				} else {
					json.NewEncoder(w).Encode(map[string]interface{}{
						"success":      true,
						"account":      accNum,
						"pairing_code": code,
					})
				}
				return
			}

			qr := startPairingAccount(accNum)
			multiLock.RLock()
			var isConn, isLog bool
			var jid string
			var targetCli *whatsmeow.Client
			if accNum <= len(allClients) && allClients[accNum-1] != nil {
				targetCli = allClients[accNum-1]
			} else if pc, exists := pairingClients[accNum]; exists {
				targetCli = pc
			}
			if targetCli != nil {
				isConn = targetCli.IsConnected()
				isLog = targetCli.IsLoggedIn()
				if targetCli.Store != nil && targetCli.Store.ID != nil {
					jid = targetCli.Store.ID.String()
				}
			}
			multiLock.RUnlock()

			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{
				"account":   accNum,
				"qr":        qr,
				"connected": isConn,
				"logged_in": isLog,
				"jid":       jid,
			})
			return
		}

		// Cuenta 1 (por defecto)
		qrLock.RLock()
		qr := currentQRCode
		qrLock.RUnlock()
		var jidStr string
		if client != nil && client.Store != nil && client.Store.ID != nil {
			jidStr = client.Store.ID.String()
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"account":   1,
			"qr":        qr,
			"connected": client != nil && client.IsConnected(),
			"logged_in": client != nil && client.IsLoggedIn(),
			"jid":       jidStr,
		})
	})

	// Endpoint para listar todas las cuentas de WhatsApp conectadas
	http.HandleFunc("/api/accounts", func(w http.ResponseWriter, r *http.Request) {
		multiLock.RLock()
		defer multiLock.RUnlock()

		type AccInfo struct {
			Index     int    `json:"index"`
			Phone     string `json:"phone"`
			JID       string `json:"jid"`
			Connected bool   `json:"connected"`
			LoggedIn  bool   `json:"logged_in"`
		}

		var accs []AccInfo
		for i, c := range allClients {
			if c != nil && c.Store != nil && c.Store.ID != nil && c.Store.ID.User != "" {
				accs = append(accs, AccInfo{
					Index:     i + 1,
					Phone:     c.Store.ID.User,
					JID:       c.Store.ID.String(),
					Connected: c.IsConnected(),
					LoggedIn:  c.IsLoggedIn(),
				})
			}
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success":  true,
			"total":    len(accs),
			"accounts": accs,
		})
	})

	// Página web interactiva para vincular Cuenta 2 (o cualquier cuenta)
	http.HandleFunc("/pair/", func(w http.ResponseWriter, r *http.Request) {
		parts := strings.TrimPrefix(r.URL.Path, "/pair/")
		if parts == "favicon.ico" {
			w.WriteHeader(http.StatusNotFound)
			return
		}
		accNum := 2
		if n, err := strconv.Atoi(parts); err == nil && n >= 2 {
			accNum = n
		}

		qr := startPairingAccount(accNum)
		w.Header().Set("Content-Type", "text/html; charset=utf-8")

		multiLock.RLock()
		var loggedIn bool
		if accNum <= len(allClients) && allClients[accNum-1] != nil {
			loggedIn = allClients[accNum-1].IsLoggedIn()
		}
		multiLock.RUnlock()

		accTitle := strconv.Itoa(accNum)
		html := `<!DOCTYPE html>
<html lang="es">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Vincular Cuenta ` + accTitle + ` - WhatsApp Bridge</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; background: #0f172a; color: #f8fafc; display: flex; flex-direction: column; align-items: center; justify-content: center; min-height: 100vh; margin: 0; padding: 20px; box-sizing: border-box; }
        .card { background: #1e293b; border: 1px solid #334155; border-radius: 16px; padding: 32px; max-width: 440px; width: 100%; text-align: center; box-shadow: 0 10px 25px -5px rgba(0,0,0,0.3); }
        h1 { margin-top: 0; font-size: 24px; color: #38bdf8; }
        .badge { display: inline-block; padding: 6px 16px; border-radius: 9999px; font-weight: 600; font-size: 14px; margin-bottom: 24px; }
        .connected { background: #065f46; color: #34d399; }
        .waiting { background: #854d0e; color: #fde047; }
        .qr-container { background: #ffffff; padding: 16px; border-radius: 12px; display: inline-block; margin-bottom: 20px; }
        .qr-container img { width: 280px; height: 280px; display: block; }
        p { color: #94a3b8; font-size: 14px; line-height: 1.5; margin: 0 0 16px; }
    </style>
</head>
<body>
    <div class="card">
        <h1>Vincular Cuenta ` + accTitle + ` de WhatsApp</h1>`

		if loggedIn {
			html += `
        <div class="badge connected">✓ CUENTA ` + accTitle + ` CONECTADA</div>
        <p>Esta cuenta de WhatsApp ya está vinculada y lista para publicar estados en simultáneo.</p>`
		} else if qr != "" {
			qrImgURL := "https://api.qrserver.com/v1/create-qr-code/?size=300x300&data=" + url.QueryEscape(qr)
			html += `
        <div class="badge waiting">⏳ ESCANEAR CON WHATSAPP #` + accTitle + `</div>
        <p>Abre tu segundo WhatsApp > <b>Dispositivos vinculados</b> > <b>Vincular un dispositivo</b> y escanea este código:</p>
        <div class="qr-container">
            <img src="` + qrImgURL + `" alt="QR Code Cuenta ` + accTitle + `" />
        </div>
        <p>El código se actualiza automáticamente.</p>
        <script>setTimeout(function(){ location.reload(); }, 4000);</script>`
		} else {
			html += `
        <div class="badge waiting">⏳ INICIANDO EMPAREJAMIENTO...</div>
        <p>Generando código de vinculación para la segunda cuenta. Espera unos segundos...</p>
        <script>setTimeout(function(){ location.reload(); }, 3000);</script>`
		}

		html += `
    </div>
</body>
</html>`
		w.Write([]byte(html))
	})

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" {
			http.NotFound(w, r)
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		qrLock.RLock()
		qr := currentQRCode
		qrLock.RUnlock()
		loggedIn := client != nil && client.IsLoggedIn()

		html := `<!DOCTYPE html>
<html lang="es">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>WhatsApp Cloud Bridge</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; background: #0f172a; color: #f8fafc; display: flex; flex-direction: column; align-items: center; justify-content: center; min-height: 100vh; margin: 0; padding: 20px; box-sizing: border-box; }
        .card { background: #1e293b; border: 1px solid #334155; border-radius: 16px; padding: 32px; max-width: 440px; width: 100%; text-align: center; box-shadow: 0 10px 25px -5px rgba(0,0,0,0.3); }
        h1 { margin-top: 0; font-size: 24px; color: #38bdf8; }
        .status-badge { display: inline-block; padding: 6px 16px; border-radius: 9999px; font-weight: 600; font-size: 14px; margin-bottom: 24px; }
        .status-connected { background: #065f46; color: #34d399; }
        .status-waiting { background: #854d0e; color: #fde047; }
        .qr-container { background: #ffffff; padding: 16px; border-radius: 12px; display: inline-block; margin-bottom: 20px; }
        .qr-container img { width: 280px; height: 280px; display: block; }
        p { color: #94a3b8; font-size: 14px; line-height: 1.5; margin: 0 0 16px; }
        .meta { font-size: 12px; color: #64748b; margin-top: 16px; }
    </style>
</head>
<body>
    <div class="card">
        <h1>WhatsApp Cloud Bridge</h1>`
		if loggedIn {
			html += `
        <div class="status-badge status-connected">✓ CONECTADO A WHATSAPP</div>
        <p>El puente en la nube está enlazado correctamente con WhatsApp y listo para recibir envíos desde Telegram.</p>
        <p style="color: #38bdf8; font-size: 13px;">Registrado con Cloudflare Worker 24/7</p>`
		} else if qr != "" {
			qrImgURL := "https://api.qrserver.com/v1/create-qr-code/?size=300x300&data=" + url.QueryEscape(qr)
			html += fmt.Sprintf(`
        <div class="status-badge status-waiting">⏳ ESPERANDO ESCANEO</div>
        <p>Abre WhatsApp en tu teléfono > <b>Dispositivos vinculados</b> > <b>Vincular un dispositivo</b> y escanea este código:</p>
        <div class="qr-container">
            <img src="%s" alt="WhatsApp QR Code" />
        </div>
        <p>El código se actualiza automáticamente.</p>
        <script>setTimeout(function(){ location.reload(); }, 4000);</script>`, qrImgURL)
		} else {
			html += `
        <div class="status-badge status-waiting">⏳ GENERANDO QR...</div>
        <p>Iniciando cliente de WhatsApp en el servidor. Por favor espera unos segundos...</p>
        <script>setTimeout(function(){ location.reload(); }, 3000);</script>`
		}
		html += `
        <div class="meta">Telegram TikTok HD Downloader &copy; 2026</div>
    </div>
</body>
</html>`
		w.Write([]byte(html))
	})

	http.HandleFunc("/api/send", func(w http.ResponseWriter, r *http.Request) {

		// Only allow POST requests

		if r.Method != http.MethodPost {

			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)

			return

		}



		// Parse the request body

		var req SendMessageRequest

		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {

			http.Error(w, "Invalid request format", http.StatusBadRequest)

			return

		}



		// Validate request

		if req.Recipient == "" {

			http.Error(w, "Recipient is required", http.StatusBadRequest)

			return

		}



		if req.Message == "" && req.MediaPath == "" {

			http.Error(w, "Message or media path is required", http.StatusBadRequest)

			return

		}



		fmt.Println("Received request to send message", req.Message, req.MediaPath)



		// Send the message

		success, message := sendWhatsAppMessage(client, req.Recipient, req.Message, req.MediaPath, req.Mentions)

		fmt.Println("Message sent", success, message)

		// Set response headers

		w.Header().Set("Content-Type", "application/json")



		// Set appropriate status code

		if !success {

			w.WriteHeader(http.StatusInternalServerError)

		}



		// Send response

		json.NewEncoder(w).Encode(SendMessageResponse{

			Success: success,

			Message: message,

		})

	})

	// Handler for querying synced contacts and status privacy for diagnostics
	http.HandleFunc("/api/contacts", func(w http.ResponseWriter, r *http.Request) {
		multiLock.RLock()
		defer multiLock.RUnlock()
		type AccContacts struct {
			Index         int      `json:"index"`
			Phone         string   `json:"phone"`
			TotalContacts int      `json:"total_contacts"`
			NamedContacts int      `json:"named_contacts"`
			PrivacyType   string   `json:"privacy_type"`
			Sample        []string `json:"sample"`
		}
		var results []AccContacts
		for i, c := range allClients {
			if c != nil && c.Store != nil && c.Store.Contacts != nil {
				phone := ""
				if c.Store.ID != nil {
					phone = c.Store.ID.ToNonAD().User
				}
				allC, _ := c.Store.Contacts.GetAllContacts(context.Background())
				namedCount := 0
				var sample []string
				for jid, contact := range allC {
					if len(contact.FullName) > 0 {
						namedCount++
						if len(sample) < 5 {
							sample = append(sample, fmt.Sprintf("%s (%s)", jid.User, contact.FullName))
						}
					}
				}
				privacyStr := "unknown"
				if priv, err := c.GetStatusPrivacy(context.Background()); err == nil && len(priv) > 0 {
					privacyStr = string(priv[0].Type)
				}
				results = append(results, AccContacts{
					Index:         i + 1,
					Phone:         phone,
					TotalContacts: len(allC),
					NamedContacts: namedCount,
					PrivacyType:   privacyStr,
					Sample:        sample,
				})
			}
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(results)
	})

	// Handler to inspect status privacy and contact status
	http.HandleFunc("/api/privacy-debug", func(w http.ResponseWriter, r *http.Request) {
		multiLock.RLock()
		defer multiLock.RUnlock()
		type AccDebug struct {
			Index            int                   `json:"index"`
			Phone            string                `json:"phone"`
			PrivacyOptions   []types.StatusPrivacy `json:"privacy_options"`
			BlacklistUsers   []string              `json:"blacklist_users"`
			BlacklistCount   int                   `json:"blacklist_count"`
			LIDMapCount      int                   `json:"lid_map_count"`
			TotalContacts    int                   `json:"total_contacts"`
			NamedContacts    int                   `json:"named_contacts"`
			ContactsSample   []map[string]string   `json:"contacts_sample"`
			BlacklistMatches []string              `json:"blacklist_matches"`
		}
		var out []AccDebug
		for i, c := range allClients {
			if c != nil {
				phone := ""
				if c.Store != nil && c.Store.ID != nil {
					phone = c.Store.ID.ToNonAD().User
				}
				priv, err := c.GetStatusPrivacy(context.Background())
				if err != nil {
					fmt.Printf("[PrivacyDebug] Acc %d GetStatusPrivacy err: %v\n", i+1, err)
				}
				var blUsers []string
				blMap := make(map[string]bool)
				for _, p := range priv {
					if p.Type == types.StatusPrivacyTypeBlacklist {
						for _, j := range p.List {
							u := strings.TrimSpace(j.User)
							if u != "" && !blMap[u] {
								blMap[u] = true
								blUsers = append(blUsers, fmt.Sprintf("%s@%s", u, j.Server))
							}
						}
					}
				}

				lidMapCount := 0
				db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
				if err == nil {
					_ = db.QueryRow("SELECT COUNT(*) FROM whatsmeow_lid_map").Scan(&lidMapCount)
					db.Close()
				}

				allC, _ := c.Store.Contacts.GetAllContacts(context.Background())
				namedCount := 0
				var sample []map[string]string
				var blMatches []string
				for jid, contact := range allC {
					if len(contact.FullName) > 0 {
						namedCount++
					}
					if blMap[jid.User] {
						blMatches = append(blMatches, fmt.Sprintf("%s (%s / %s)", jid.String(), contact.FullName, contact.PushName))
					}
					if len(sample) < 15 {
						sample = append(sample, map[string]string{
							"jid":       jid.String(),
							"full_name": contact.FullName,
							"push_name": contact.PushName,
						})
					}
				}

				out = append(out, AccDebug{
					Index:            i + 1,
					Phone:            phone,
					PrivacyOptions:   priv,
					BlacklistUsers:   blUsers,
					BlacklistCount:   len(blUsers),
					LIDMapCount:      lidMapCount,
					TotalContacts:    len(allC),
					NamedContacts:    namedCount,
					ContactsSample:   sample,
					BlacklistMatches: blMatches,
				})
			}
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(out)
	})

	// Handler to return status views and viewer analytics
	http.HandleFunc("/api/status-views", func(w http.ResponseWriter, r *http.Request) {
		multiLock.RLock()
		defer multiLock.RUnlock()

		targetAcc := r.URL.Query().Get("account") // optional: "1", "2", or phone number
		limitStr := r.URL.Query().Get("limit")
		limit := 5
		if l, err := strconv.Atoi(limitStr); err == nil && l > 0 && l <= 20 {
			limit = l
		}

		db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
		if err != nil {
			http.Error(w, fmt.Sprintf("Database error: %v", err), http.StatusInternalServerError)
			return
		}
		defer db.Close()

		type ViewerDetail struct {
			Phone    string `json:"phone"`
			Name     string `json:"name"`
			ViewedAt string `json:"viewed_at"`
			TimeAgo  string `json:"time_ago"`
		}

		type StatusSummary struct {
			StatusID     string         `json:"status_id"`
			AccountPhone string         `json:"account_phone"`
			AccountIndex int            `json:"account_index"`
			Caption      string         `json:"caption"`
			MediaType    string         `json:"media_type"`
			CreatedAt    string         `json:"created_at"`
			TimeAgo      string         `json:"time_ago"`
			TotalViews   int            `json:"total_views"`
			Viewers      []ViewerDetail `json:"viewers"`
		}

		phoneToIdx := make(map[string]int)
		for idx, c := range allClients {
			if c != nil && c.Store != nil && c.Store.ID != nil {
				phoneToIdx[c.Store.ID.ToNonAD().User] = idx + 1
			}
		}

		query := `
			SELECT 
				id,
				account_phone,
				caption,
				media_type,
				created_at
			FROM status_posts
			ORDER BY created_at DESC
			LIMIT ?
		`

		rows, err := db.Query(query, limit)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{"success": true, "statuses": []StatusSummary{}, "total_statuses": 0})
			return
		}
		defer rows.Close()

		statuses := []StatusSummary{}
		seenStatusIDs := make(map[string]bool)

		for rows.Next() {
			var sid, accPhone, caption, mediaType string
			var createdStr sql.NullString
			if err := rows.Scan(&sid, &accPhone, &caption, &mediaType, &createdStr); err != nil {
				continue
			}

			if targetAcc != "" {
				idxMatch := strconv.Itoa(phoneToIdx[accPhone])
				if targetAcc != accPhone && targetAcc != idxMatch {
					continue
				}
			}

			seenStatusIDs[sid] = true

			cStr := ""
			if createdStr.Valid {
				cStr = createdStr.String
			}
			createdTime := parseFlexibleTime(cStr)

			vRows, vErr := db.Query(`
				SELECT viewer_phone, viewer_name, viewed_at
				FROM status_views
				WHERE status_id = ?
				ORDER BY viewed_at ASC
			`, sid)

			viewers := []ViewerDetail{}
			if vErr == nil {
				for vRows.Next() {
					var vPhone, vName, vTimeStr string
					if err := vRows.Scan(&vPhone, &vName, &vTimeStr); err == nil {
						vTime := parseFlexibleTime(vTimeStr)
						viewers = append(viewers, ViewerDetail{
							Phone:    vPhone,
							Name:     vName,
							ViewedAt: vTimeStr,
							TimeAgo:  formatTimeAgo(vTime),
						})
					}
				}
				vRows.Close()
			}

			statuses = append(statuses, StatusSummary{
				StatusID:     sid,
				AccountPhone: accPhone,
				AccountIndex: phoneToIdx[accPhone],
				Caption:      caption,
				MediaType:    mediaType,
				CreatedAt:    cStr,
				TimeAgo:      formatTimeAgo(createdTime),
				TotalViews:   len(viewers),
				Viewers:      viewers,
			})
		}

		// Also check any orphan status_views whose status_id wasn't in status_posts
		orphanRows, oErr := db.Query(`
			SELECT status_id, account_phone, MIN(viewed_at) as first_view
			FROM status_views
			GROUP BY status_id
			ORDER BY first_view DESC
			LIMIT ?
		`, limit)
		if oErr == nil {
			defer orphanRows.Close()
			for orphanRows.Next() {
				var sid, accPhone, firstViewStr string
				if err := orphanRows.Scan(&sid, &accPhone, &firstViewStr); err == nil {
					if seenStatusIDs[sid] {
						continue
					}
					if targetAcc != "" {
						idxMatch := strconv.Itoa(phoneToIdx[accPhone])
						if targetAcc != accPhone && targetAcc != idxMatch {
							continue
						}
					}

					vTime := parseFlexibleTime(firstViewStr)

					vRows, vErr := db.Query(`
						SELECT viewer_phone, viewer_name, viewed_at
						FROM status_views
						WHERE status_id = ?
						ORDER BY viewed_at ASC
					`, sid)
					viewers := []ViewerDetail{}
					if vErr == nil {
						for vRows.Next() {
							var vPhone, vName, vTimeStr string
							if err := vRows.Scan(&vPhone, &vName, &vTimeStr); err == nil {
								vt := parseFlexibleTime(vTimeStr)
								viewers = append(viewers, ViewerDetail{
									Phone:    vPhone,
									Name:     vName,
									ViewedAt: vTimeStr,
									TimeAgo:  formatTimeAgo(vt),
								})
							}
						}
						vRows.Close()
					}

					statuses = append(statuses, StatusSummary{
						StatusID:     sid,
						AccountPhone: accPhone,
						AccountIndex: phoneToIdx[accPhone],
						Caption:      "Estado de WhatsApp",
						MediaType:    "media",
						CreatedAt:    firstViewStr,
						TimeAgo:      formatTimeAgo(vTime),
						TotalViews:   len(viewers),
						Viewers:      viewers,
					})
				}
			}
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success":        true,
			"total_statuses": len(statuses),
			"statuses":       statuses,
		})
	})

	// Handler to manually trigger privacy enforcement on all accounts
	http.HandleFunc("/api/sanitize-privacy", func(w http.ResponseWriter, r *http.Request) {
		multiLock.Lock()
		defer multiLock.Unlock()
		var logs []string
		for i, c := range allClients {
			if c != nil && c.IsConnected() {
				phone := ""
				if c.Store != nil && c.Store.ID != nil {
					phone = c.Store.ID.ToNonAD().User
				}
				count, err := sanitizeContactsForStatusPrivacy(c)
				if err != nil {
					logs = append(logs, fmt.Sprintf("Acc %d (%s) Error: %v", i+1, phone, err))
				} else {
					logs = append(logs, fmt.Sprintf("Acc %d (%s) Success: %d excluded contacts protected", i+1, phone, count))
				}
			}
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{"status": "success", "logs": logs})
	})

	// Handler to force AppState sync to download contacts from WhatsApp
	http.HandleFunc("/api/sync-contacts", func(w http.ResponseWriter, r *http.Request) {
		multiLock.RLock()
		defer multiLock.RUnlock()
		var logs []string
		for i, c := range allClients {
			if c != nil && c.IsConnected() {
				phone := ""
				if c.Store != nil && c.Store.ID != nil {
					phone = c.Store.ID.ToNonAD().User
				}
				for _, patch := range appstate.AllPatchNames {
					if err := c.FetchAppState(context.Background(), patch, false, false); err != nil {
						logs = append(logs, fmt.Sprintf("Acc %d (%s) Patch %s: %v", i+1, phone, patch, err))
					} else {
						logs = append(logs, fmt.Sprintf("Acc %d (%s) Patch %s: synced OK", i+1, phone, patch))
					}
				}
			}
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{"status": "done", "logs": logs})
	})

	// Handler to reset/clean Account 2 contacts so accounts remain 100% isolated
	http.HandleFunc("/api/reset-account2-contacts", func(w http.ResponseWriter, r *http.Request) {
		multiLock.Lock()
		defer multiLock.Unlock()
		if len(allClients) > 1 && allClients[1] != nil && allClients[1].Store != nil && allClients[1].Store.ID != nil {
			acc2JID := allClients[1].Store.ID.String()
			db, err := sql.Open("sqlite", "file:store/whatsapp.db?_pragma=busy_timeout(5000)")
			if err == nil {
				defer db.Close()
				res, _ := db.Exec("DELETE FROM whatsmeow_contacts WHERE our_jid = ?", acc2JID)
				rows := int64(0)
				if res != nil {
					rows, _ = res.RowsAffected()
				}
				w.Header().Set("Content-Type", "application/json")
				json.NewEncoder(w).Encode(map[string]interface{}{"status": "success", "account2_contacts_deleted": rows})
				return
			}
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{"status": "not_applicable"})
	})

	// Handler to extract YouTube & YouTube Shorts using yt-dlp
	http.HandleFunc("/api/extract-youtube", func(w http.ResponseWriter, r *http.Request) {
		targetURL := r.URL.Query().Get("url")
		if targetURL == "" && r.Method == http.MethodPost {
			var body struct {
				URL string `json:"url"`
			}
			json.NewDecoder(r.Body).Decode(&body)
			targetURL = body.URL
		}
		if targetURL == "" {
			http.Error(w, "Parameter 'url' is required", http.StatusBadRequest)
			return
		}

		ytBin, err := ensureYtDlp()
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{"success": false, "error": err.Error()})
			return
		}

		// Extract YouTube ID
		re := regexp.MustCompile(`(?:shorts/|v=|youtu\.be/|embed/)([a-zA-Z0-9_-]{11})`)
		matches := re.FindStringSubmatch(targetURL)
		vidID := "yt_clip"
		if len(matches) > 1 {
			vidID = matches[1]
		} else {
			vidID = fmt.Sprintf("yt_%d", time.Now().UnixNano())
		}

		outputPath := filepath.Join(os.TempDir(), fmt.Sprintf("yt_%s.mp4", vidID))
		baseURL := "https://whatsapp-bridge-server-0ia4.onrender.com"
		if r.Host != "" {
			scheme := "https"
			if strings.HasPrefix(r.Host, "localhost") || strings.HasPrefix(r.Host, "127.0.0.1") {
				scheme = "http"
			}
			baseURL = fmt.Sprintf("%s://%s", scheme, r.Host)
		}
		publicMediaURL := fmt.Sprintf("%s/media/youtube/%s.mp4", baseURL, vidID)

		// Check if file already downloaded and valid (>100KB)
		if fi, err := os.Stat(outputPath); err == nil && fi.Size() > 100000 {
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success":   true,
				"id":        vidID,
				"video_url": publicMediaURL,
				"cached":    true,
			})
			return
		}

		ctx, cancel := context.WithTimeout(r.Context(), 50*time.Second)
		defer cancel()

		cmd := exec.CommandContext(ctx, ytBin,
			"--no-warnings",
			"--remote-components", "ejs:github",
			"-f", "bv*[ext=mp4]+ba[ext=m4a]/bv*+ba/b",
			"--merge-output-format", "mp4",
			"-o", outputPath,
			targetURL,
		)

		var outBuf, errBuf bytes.Buffer
		cmd.Stdout = &outBuf
		cmd.Stderr = &errBuf

		if err := cmd.Run(); err != nil {
			fmt.Printf("[YT-DLP] Error extracting %s: %v | Stderr: %s\n", targetURL, err, errBuf.String())
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusBadGateway)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"error":   fmt.Sprintf("yt-dlp error: %v", err),
				"details": errBuf.String(),
			})
			return
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success":   true,
			"id":        vidID,
			"video_url": publicMediaURL,
			"cached":    false,
		})
	})

	// Handler to serve downloaded YouTube MP4 files directly to Telegram & WhatsApp
	http.HandleFunc("/media/youtube/", func(w http.ResponseWriter, r *http.Request) {
		name := strings.TrimPrefix(r.URL.Path, "/media/youtube/")
		name = strings.TrimSuffix(name, ".mp4")
		re := regexp.MustCompile(`^[a-zA-Z0-9_-]+$`)
		if !re.MatchString(name) {
			http.NotFound(w, r)
			return
		}
		targetFile := filepath.Join(os.TempDir(), fmt.Sprintf("yt_%s.mp4", name))
		if _, err := os.Stat(targetFile); os.IsNotExist(err) {
			http.NotFound(w, r)
			return
		}
		w.Header().Set("Content-Type", "video/mp4")
		http.ServeFile(w, r, targetFile)
	})

	// Handler for publishing to WhatsApp (Status & Nick chat) directly from Cloudflare Worker
	http.HandleFunc("/api/publish", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		type PublishReq struct {
			Action    string   `json:"action"` // "st", "st1", "st2", "both", "nk"
			Account   int      `json:"account,omitempty"` // 1, 2, or 0 (both)
			VideoID   string   `json:"video_id"`
			VideoURL  string   `json:"video_url"`
			Images    []string `json:"images,omitempty"`
			IsImages  bool     `json:"is_images,omitempty"`
			Title     string   `json:"title"`
			Author    string   `json:"author"`
			Platform  string   `json:"platform"`
			Recipient string   `json:"recipient"` // Optional dynamic recipient
			Caption   string   `json:"caption,omitempty"` // Optional custom caption
		}

		var req PublishReq
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		if req.VideoURL == "" && len(req.Images) == 0 {
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": "No se proporcionó URL del video o imágenes para publicar",
			})
			return
		}

		// Dynamic recipient resolution for private chat (only if action == "nk")
		var targetRecipient string
		if req.Recipient != "" {
			targetRecipient = req.Recipient
		} else if client != nil && client.Store != nil && client.Store.ID != nil {
			targetRecipient = client.Store.ID.ToNonAD().String()
		} else if envPhone := os.Getenv("NICK_PHONE"); envPhone != "" {
			targetRecipient = envPhone
		} else {
			targetRecipient = "51917515837"
		}
		if !strings.Contains(targetRecipient, "@") {
			targetRecipient = targetRecipient + "@s.whatsapp.net"
		}

		statusBroadcast := "status@broadcast"

		// Limpiar hashtags del título para que no salgan palabras como #fyp #viral #lyrics
		rawTitle := strings.TrimSpace(req.Title)
		var cleanWords []string
		for _, w := range strings.Fields(rawTitle) {
			if !strings.HasPrefix(w, "#") {
				cleanWords = append(cleanWords, w)
			}
		}
		cleanTitle := strings.TrimSpace(strings.Join(cleanWords, " "))
		if len(cleanTitle) > 200 {
			cleanTitle = cleanTitle[:200] + "..."
		}

		platformName := strings.TrimSpace(req.Platform)
		if platformName == "" {
			platformName = "Social Media HD"
		}
		authorName := strings.TrimSpace(req.Author)
		if authorName == "" {
			authorName = "Creador"
		}

		// Formato Profesional para WhatsApp Personal
		var personalMsg string
		if req.Caption != "" {
			personalMsg = req.Caption
		} else if cleanTitle != "" {
			personalMsg = fmt.Sprintf("🎬 *%s*\n\n👤 *Autor:* %s\n📱 *Plataforma:* %s\n━━━━━━━━━━━━━━━━━━━━\n⚡ *Descargado con @clianythingbot*", cleanTitle, authorName, platformName)
		} else {
			personalMsg = fmt.Sprintf("👤 *Autor:* %s\n📱 *Plataforma:* %s\n━━━━━━━━━━━━━━━━━━━━\n⚡ *Descargado con @clianythingbot*", authorName, platformName)
		}

		var errs []string
		var successAccNames []string

		// 1. PUBLICAR EN ESTADO DE WHATSAPP (st, st1, st2, both)
		isStatusAction := req.Action == "st" || req.Action == "st1" || req.Action == "st2" || req.Action == "both" || strings.HasPrefix(req.Action, "st")
		if isStatusAction {
			mediaToStatus := req.VideoURL
			if mediaToStatus == "" && len(req.Images) > 0 {
				mediaToStatus = req.Images[0]
			}
			statusCaption := req.Caption

			allLoggedIn := getLoggedInClients()
			if len(allLoggedIn) == 0 && client != nil {
				allLoggedIn = append(allLoggedIn, client)
			}

			// Determinar a qué cuenta(s) dirigir la publicación
			targetAcc := req.Account
			if req.Action == "st1" {
				targetAcc = 1
			} else if req.Action == "st2" {
				targetAcc = 2
			}

			type accTarget struct {
				index  int
				client *whatsmeow.Client
			}
			var targets []accTarget

			if targetAcc > 0 {
				if targetAcc <= len(allLoggedIn) && allLoggedIn[targetAcc-1] != nil {
					targets = append(targets, accTarget{index: targetAcc, client: allLoggedIn[targetAcc-1]})
				} else {
					errs = append(errs, fmt.Sprintf("La Cuenta %d no se encuentra conectada", targetAcc))
				}
			} else {
				for i, c := range allLoggedIn {
					if c != nil {
						targets = append(targets, accTarget{index: i + 1, client: c})
					}
				}
			}

			for _, t := range targets {
				c := t.client
				if c != nil && c.IsConnected() {
					phone := ""
					if c.Store != nil && c.Store.ID != nil {
						phone = c.Store.ID.ToNonAD().User
					}
					ok, msg := sendWhatsAppMessage(c, statusBroadcast, statusCaption, mediaToStatus, nil)
					if !ok {
						errs = append(errs, fmt.Sprintf("Cuenta %d (%s): %s", t.index, phone, msg))
					} else {
						tag := fmt.Sprintf("Cuenta %d (%s)", t.index, phone)
						successAccNames = append(successAccNames, tag)
						fmt.Printf("[Bridge Cloud] ¡Publicado en Estado de %s con éxito!\n", tag)
					}
				}
			}
		}

		// 2. ENVIAR A CHAT PERSONAL DE WHATSAPP (SOLO SI SE SOLICITA EXPLÍCITAMENTE "nk")
		if req.Action == "nk" {
			if req.VideoURL != "" && !req.IsImages {
				ok, msg := sendWhatsAppMessage(client, targetRecipient, personalMsg, req.VideoURL, nil)
				if !ok {
					errs = append(errs, fmt.Sprintf("Personal Video: %s", msg))
				} else {
					fmt.Printf("[Bridge Cloud] ¡Video enviado a %s con éxito!\n", targetRecipient)
				}
			} else if len(req.Images) > 0 {
				totalImgs := len(req.Images)
				if totalImgs > 10 {
					totalImgs = 10
				}
				for idx := 0; idx < totalImgs; idx++ {
					imgURL := req.Images[idx]
					caption := ""
					if idx == 0 {
						caption = personalMsg
					} else {
						caption = fmt.Sprintf("📸 Foto %d/%d", idx+1, totalImgs)
					}
					ok, msg := sendWhatsAppMessage(client, targetRecipient, caption, imgURL, nil)
					if !ok {
						errs = append(errs, fmt.Sprintf("Foto %d: %s", idx+1, msg))
					}
					time.Sleep(300 * time.Millisecond)
				}
				fmt.Printf("[Bridge Cloud] ¡Carrusel de %d fotos enviado a %s!\n", totalImgs, targetRecipient)
			} else if req.VideoURL != "" {
				ok, msg := sendWhatsAppMessage(client, targetRecipient, personalMsg, req.VideoURL, nil)
				if !ok {
					errs = append(errs, fmt.Sprintf("Personal: %s", msg))
				} else {
					fmt.Printf("[Bridge Cloud] ¡Enviado a %s con éxito!\n", targetRecipient)
				}
			}
		}

		cleanPhone := strings.TrimSuffix(targetRecipient, "@s.whatsapp.net")
		cleanPhone = strings.TrimSuffix(cleanPhone, "@lid")

		w.Header().Set("Content-Type", "application/json")
		if len(errs) > 0 && len(successAccNames) == 0 {
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success":   false,
				"message":   strings.Join(errs, ", "),
				"recipient": cleanPhone,
			})
		} else {
			respMsg := "Publicado exitosamente en Estado de WhatsApp"
			if len(successAccNames) > 0 {
				respMsg = fmt.Sprintf("Publicado exitosamente en: %s", strings.Join(successAccNames, " y "))
			}
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success":            true,
				"message":            respMsg,
				"accounts_published": successAccNames,
				"recipient":          cleanPhone,
				"wa_link":            fmt.Sprintf("https://wa.me/%s", cleanPhone),
			})
		}
	})



	// Handler for downloading media

	http.HandleFunc("/api/download", func(w http.ResponseWriter, r *http.Request) {

		// Only allow POST requests

		if r.Method != http.MethodPost {

			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)

			return

		}



		// Parse the request body

		var req DownloadMediaRequest

		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {

			http.Error(w, "Invalid request format", http.StatusBadRequest)

			return

		}



		// Validate request

		if req.MessageID == "" || req.ChatJID == "" {

			http.Error(w, "Message ID and Chat JID are required", http.StatusBadRequest)

			return

		}



		// Download the media

		success, mediaType, filename, path, err := downloadMedia(client, messageStore, req.MessageID, req.ChatJID)



		// Set response headers

		w.Header().Set("Content-Type", "application/json")



		// Handle download result

		if !success || err != nil {

			errMsg := "Unknown error"

			if err != nil {

				errMsg = err.Error()

			}



			w.WriteHeader(http.StatusInternalServerError)

			json.NewEncoder(w).Encode(DownloadMediaResponse{

				Success: false,

				Message: fmt.Sprintf("Failed to download media: %s", errMsg),

			})

			return

		}



		// Send successful response

		json.NewEncoder(w).Encode(DownloadMediaResponse{

			Success:  true,

			Message:  fmt.Sprintf("Successfully downloaded %s media", mediaType),

			Filename: filename,

			Path:     path,

		})

	})



	// Start the server

	serverAddr := fmt.Sprintf(":%d", port)

	fmt.Printf("Starting REST API server on %s...\n", serverAddr)



	// Run server in a goroutine so it doesn't block

	go func() {

		if err := http.ListenAndServe(serverAddr, nil); err != nil {

			fmt.Printf("REST API server error: %v\n", err)

		}

	}()

}



func main() {

	// Set official Chrome on Windows OS info so WhatsApp doesn't block device pairing

	store.SetOSInfo("Windows", [3]uint32{10, 0, 22631})

	store.DeviceProps.PlatformType = waCompanionReg.DeviceProps_CHROME.Enum()



	// Set up logger

	logger := waLog.Stdout("Client", "INFO", true)

	logger.Infof("Starting WhatsApp client...")



	// Create database connection for storing session data

	dbLog := waLog.Stdout("Database", "INFO", true)



	// Create directory for database if it doesn't exist
	if err := os.MkdirAll("store", 0755); err != nil {
		logger.Errorf("Failed to create store directory: %v", err)
		return
	}

	// Restaurar sesión de WhatsApp desde Cloudflare KV si la base de datos local no existe o está incompleta (< 100 KB)
	if fi, err := os.Stat("store/whatsapp.db"); os.IsNotExist(err) || fi.Size() < 100000 {
		restoreSessionFromWorker()
	}

	container, err := sqlstore.New(context.Background(), "sqlite", "file:store/whatsapp.db?_pragma=foreign_keys(1)&_pragma=journal_mode(DELETE)&_pragma=busy_timeout(10000)", dbLog)
	if err != nil {
		logger.Errorf("Failed to connect to database: %v", err)
		return
	}

	globalContainer = container
	globalLogger = logger

	// Get device stores - This contains session information
	devices, err := container.GetAllDevices(context.Background())
	if err != nil {
		logger.Errorf("Failed to get devices: %v", err)
		return
	}
	if len(devices) == 0 {
		dev := container.NewDevice()
		devices = append(devices, dev)
		logger.Infof("Created new device")
	}

	deviceStore := devices[0]

	// Create primary client
	client := whatsmeow.NewClient(deviceStore, logger)
	if client == nil {
		logger.Errorf("Failed to create WhatsApp client")
		return
	}
	setupClientEventHandlers(client)

	multiLock.Lock()
	allClients = append(allClients, client)
	for i := 1; i < len(devices); i++ {
		dev := devices[i]
		if dev.ID != nil && dev.ID.User != "" {
			secCli := whatsmeow.NewClient(dev, logger)
			setupClientEventHandlers(secCli)
			allClients = append(allClients, secCli)
			go func(idx int, c *whatsmeow.Client) {
				if err := c.Connect(); err != nil {
					logger.Errorf("Failed to connect account %d: %v", idx+1, err)
				} else {
					logger.Infof("Account %d connected with JID: %s", idx+1, c.Store.ID.String())
				}
			}(i, secCli)
		}
	}
	multiLock.Unlock()

	// Initialize message store and status analytics DB
	messageStore, err := NewMessageStore()
	if err != nil {
		logger.Errorf("Failed to initialize message store: %v", err)
		return
	}
	defer messageStore.Close()
	_ = initStatusTrackerDB()

	// Start REST API server immediately so Cloud hosts (like Render) detect open port instantly
	startRESTServer(client, messageStore, 8080)

	// Background connection & pairing logic
	go func() {
		for {
			if client.IsLoggedIn() {
				logger.Infof("Client is logged in. Exiting pairing loop.")
				qrLock.Lock()
				currentQRCode = ""
				qrLock.Unlock()
				go backupSessionToWorker(client)
				break
			}

			if deviceStore.ID == nil {
				qrChan, err := client.GetQRChannel(context.Background())
				if err != nil {
					logger.Errorf("Failed to get QR channel: %v", err)
					time.Sleep(3 * time.Second)
					continue
				}

				if !client.IsConnected() {
					err = client.Connect()
					if err != nil {
						logger.Errorf("Failed to connect: %v", err)
						time.Sleep(3 * time.Second)
						continue
					}
				}

				for evt := range qrChan {
					if evt.Event == "code" {
						qrLock.Lock()
						currentQRCode = evt.Code
						qrLock.Unlock()
						fmt.Println("\nScan this QR code with your WhatsApp app:")
						qrterminal.GenerateHalfBlock(evt.Code, qrterminal.L, os.Stdout)
					} else if evt.Event == "success" {
						qrLock.Lock()
						currentQRCode = ""
						qrLock.Unlock()
						logger.Infof("QR pairing success!")
						go registerBridgeWithWorker()
						go backupSessionToWorker(client)
						return
					} else {
						logger.Warnf("QRChannel event: %s (err: %v)", evt.Event, evt.Error)
					}
				}

				// Si el canal de QR finalizó sin emparejamiento, reiniciar para generar un QR nuevo
				qrLock.Lock()
				currentQRCode = ""
				qrLock.Unlock()
				if !client.IsLoggedIn() {
					client.Disconnect()
					time.Sleep(2 * time.Second)
				}
			} else {
				err := client.Connect()
				if err != nil {
					logger.Errorf("Failed to connect: %v", err)
					time.Sleep(5 * time.Second)
					continue
				}
				go registerBridgeWithWorker()
				break
			}
		}

		// Wait for connection to stabilize
		for i := 0; i < 30; i++ {
			if client.IsConnected() {
				break
			}
			time.Sleep(500 * time.Millisecond)
		}
		if client.IsConnected() && client.Store != nil && client.Store.ID != nil {
			logger.Infof("WhatsApp client successfully connected and online with JID: %s", client.Store.ID.String())
			go backupSessionToWorker(client)
		}
	}()

	// Create a channel to keep the main goroutine alive
	exitChan := make(chan os.Signal, 1)
	signal.Notify(exitChan, syscall.SIGINT, syscall.SIGTERM)

	fmt.Println("REST server is running. Press Ctrl+C to disconnect and exit.")

	// Wait for termination signal
	<-exitChan

	fmt.Println("Disconnecting...")
	client.Disconnect()

}



// GetChatName determines the appropriate name for a chat based on JID and other info

func GetChatName(client *whatsmeow.Client, messageStore *MessageStore, jid types.JID, chatJID string, conversation interface{}, sender string, logger waLog.Logger) string {

	// First, check if chat already exists in database with a name

	var existingName string

	err := messageStore.db.QueryRow("SELECT name FROM chats WHERE jid = ?", chatJID).Scan(&existingName)

	if err == nil && existingName != "" {

		// Chat exists with a name, use that

		logger.Infof("Using existing chat name for %s: %s", chatJID, existingName)

		return existingName

	}



	// Need to determine chat name

	var name string



	if jid.Server == "g.us" {

		// This is a group chat

		logger.Infof("Getting name for group: %s", chatJID)



		// Use conversation data if provided (from history sync)

		if conversation != nil {

			// Extract name from conversation if available

			// This uses type assertions to handle different possible types

			var displayName, convName *string

			// Try to extract the fields we care about regardless of the exact type

			v := reflect.ValueOf(conversation)

			if v.Kind() == reflect.Ptr && !v.IsNil() {

				v = v.Elem()



				// Try to find DisplayName field

				if displayNameField := v.FieldByName("DisplayName"); displayNameField.IsValid() && displayNameField.Kind() == reflect.Ptr && !displayNameField.IsNil() {

					dn := displayNameField.Elem().String()

					displayName = &dn

				}



				// Try to find Name field

				if nameField := v.FieldByName("Name"); nameField.IsValid() && nameField.Kind() == reflect.Ptr && !nameField.IsNil() {

					n := nameField.Elem().String()

					convName = &n

				}

			}



			// Use the name we found

			if displayName != nil && *displayName != "" {

				name = *displayName

			} else if convName != nil && *convName != "" {

				name = *convName

			}

		}



		// If we didn't get a name, try group info

		if name == "" {

			groupInfo, err := client.GetGroupInfo(context.Background(), jid)

			if err == nil && groupInfo.Name != "" {

				name = groupInfo.Name

			} else {

				// Fallback name for groups

				name = fmt.Sprintf("Group %s", jid.User)

			}

		}



		logger.Infof("Using group name: %s", name)

	} else {

		// This is an individual contact

		logger.Infof("Getting name for contact: %s", chatJID)



		// Just use contact info (full name)

		contact, err := client.Store.Contacts.GetContact(context.Background(), jid)

		if err == nil && contact.FullName != "" {

			name = contact.FullName

		} else if sender != "" {

			// Fallback to sender

			name = sender

		} else {

			// Last fallback to JID

			name = jid.User

		}



		logger.Infof("Using contact name: %s", name)

	}



	return name

}



// Handle history sync events

func handleHistorySync(client *whatsmeow.Client, messageStore *MessageStore, historySync *events.HistorySync, logger waLog.Logger) {

	fmt.Printf("Received history sync event with %d conversations\n", len(historySync.Data.Conversations))



	syncedCount := 0

	for _, conversation := range historySync.Data.Conversations {

		// Parse JID from the conversation

		if conversation.ID == nil {

			continue

		}



		chatJID := *conversation.ID



		// Try to parse the JID

		jid, err := types.ParseJID(chatJID)

		if err != nil {

			logger.Warnf("Failed to parse JID %s: %v", chatJID, err)

			continue

		}



		// Get appropriate chat name by passing the history sync conversation directly

		name := GetChatName(client, messageStore, jid, chatJID, conversation, "", logger)



		// Process messages

		messages := conversation.Messages

		if len(messages) > 0 {

			// Update chat with latest message timestamp

			latestMsg := messages[0]

			if latestMsg == nil || latestMsg.Message == nil {

				continue

			}



			// Get timestamp from message info

			timestamp := time.Time{}

			if ts := latestMsg.Message.GetMessageTimestamp(); ts != 0 {

				timestamp = time.Unix(int64(ts), 0)

			} else {

				continue

			}



			messageStore.StoreChat(chatJID, name, timestamp)



			// Store messages

			for _, msg := range messages {

				if msg == nil || msg.Message == nil {

					continue

				}



				// Extract text content

				var content string

				if msg.Message.Message != nil {

					if conv := msg.Message.Message.GetConversation(); conv != "" {

						content = conv

					} else if ext := msg.Message.Message.GetExtendedTextMessage(); ext != nil {

						content = ext.GetText()

					}

				}



				// Extract media info

				var mediaType, filename, url string

				var mediaKey, fileSHA256, fileEncSHA256 []byte

				var fileLength uint64



				if msg.Message.Message != nil {

					mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength = extractMediaInfo(msg.Message.Message)

				}



				// Log the message content for debugging

				logger.Infof("Message content: %v, Media Type: %v", content, mediaType)



				// Skip messages with no content and no media

				if content == "" && mediaType == "" {

					continue

				}



				// Determine sender

				var sender string

				isFromMe := false

				if msg.Message.Key != nil {

					if msg.Message.Key.FromMe != nil {

						isFromMe = *msg.Message.Key.FromMe

					}

					if !isFromMe && msg.Message.Key.Participant != nil && *msg.Message.Key.Participant != "" {

						sender = *msg.Message.Key.Participant

					} else if isFromMe {

						sender = client.Store.ID.User

					} else {

						sender = jid.User

					}

				} else {

					sender = jid.User

				}



				// Store message

				msgID := ""

				if msg.Message.Key != nil && msg.Message.Key.ID != nil {

					msgID = *msg.Message.Key.ID

				}



				// Get message timestamp

				timestamp := time.Time{}

				if ts := msg.Message.GetMessageTimestamp(); ts != 0 {

					timestamp = time.Unix(int64(ts), 0)

				} else {

					continue

				}



				err = messageStore.StoreMessage(

					msgID,

					chatJID,

					sender,

					content,

					timestamp,

					isFromMe,

					mediaType,

					filename,

					url,

					mediaKey,

					fileSHA256,

					fileEncSHA256,

					fileLength,

				)

				if err != nil {

					logger.Warnf("Failed to store history message: %v", err)

				} else {

					syncedCount++

					// Log successful message storage

					if mediaType != "" {

						logger.Infof("Stored message: [%s] %s -> %s: [%s: %s] %s",

							timestamp.Format("2006-01-02 15:04:05"), sender, chatJID, mediaType, filename, content)

					} else {

						logger.Infof("Stored message: [%s] %s -> %s: %s",

							timestamp.Format("2006-01-02 15:04:05"), sender, chatJID, content)

					}

				}

			}

		}

	}



	fmt.Printf("History sync complete. Stored %d messages.\n", syncedCount)

}



// Request history sync from the server

func requestHistorySync(client *whatsmeow.Client) {

	if client == nil {

		fmt.Println("Client is not initialized. Cannot request history sync.")

		return

	}



	if !client.IsConnected() {

		fmt.Println("Client is not connected. Please ensure you are connected to WhatsApp first.")

		return

	}



	if client.Store.ID == nil {

		fmt.Println("Client is not logged in. Please scan the QR code first.")

		return

	}



	// Build and send a history sync request

	historyMsg := client.BuildHistorySyncRequest(nil, 100)

	if historyMsg == nil {

		fmt.Println("Failed to build history sync request.")

		return

	}



	_, err := client.SendMessage(context.Background(), types.JID{

		Server: "s.whatsapp.net",

		User:   "status",

	}, historyMsg)



	if err != nil {

		fmt.Printf("Failed to request history sync: %v\n", err)

	} else {

		fmt.Println("History sync requested. Waiting for server response...")

	}

}



// analyzeOggOpus tries to extract duration and generate a simple waveform from an Ogg Opus file

func analyzeOggOpus(data []byte) (duration uint32, waveform []byte, err error) {

	// Try to detect if this is a valid Ogg file by checking for the "OggS" signature

	// at the beginning of the file

	if len(data) < 4 || string(data[0:4]) != "OggS" {

		return 0, nil, fmt.Errorf("not a valid Ogg file (missing OggS signature)")

	}



	// Parse Ogg pages to find the last page with a valid granule position

	var lastGranule uint64

	var sampleRate uint32 = 48000 // Default Opus sample rate

	var preSkip uint16 = 0

	var foundOpusHead bool



	// Scan through the file looking for Ogg pages

	for i := 0; i < len(data); {

		// Check if we have enough data to read Ogg page header

		if i+27 >= len(data) {

			break

		}



		// Verify Ogg page signature

		if string(data[i:i+4]) != "OggS" {

			// Skip until next potential page

			i++

			continue

		}



		// Extract header fields

		granulePos := binary.LittleEndian.Uint64(data[i+6 : i+14])

		pageSeqNum := binary.LittleEndian.Uint32(data[i+18 : i+22])

		numSegments := int(data[i+26])



		// Extract segment table

		if i+27+numSegments >= len(data) {

			break

		}

		segmentTable := data[i+27 : i+27+numSegments]



		// Calculate page size

		pageSize := 27 + numSegments

		for _, segLen := range segmentTable {

			pageSize += int(segLen)

		}



		// Check if we're looking at an OpusHead packet (should be in first few pages)

		if !foundOpusHead && pageSeqNum <= 1 {

			// Look for "OpusHead" marker in this page

			pageData := data[i : i+pageSize]

			headPos := bytes.Index(pageData, []byte("OpusHead"))

			if headPos >= 0 && headPos+12 < len(pageData) {

				// Found OpusHead, extract sample rate and pre-skip

				// OpusHead format: Magic(8) + Version(1) + Channels(1) + PreSkip(2) + SampleRate(4) + ...

				headPos += 8 // Skip "OpusHead" marker

				// PreSkip is 2 bytes at offset 10

				if headPos+12 <= len(pageData) {

					preSkip = binary.LittleEndian.Uint16(pageData[headPos+10 : headPos+12])

					sampleRate = binary.LittleEndian.Uint32(pageData[headPos+12 : headPos+16])

					foundOpusHead = true

					fmt.Printf("Found OpusHead: sampleRate=%d, preSkip=%d\n", sampleRate, preSkip)

				}

			}

		}



		// Keep track of last valid granule position

		if granulePos != 0 {

			lastGranule = granulePos

		}



		// Move to next page

		i += pageSize

	}



	if !foundOpusHead {

		fmt.Println("Warning: OpusHead not found, using default values")

	}



	// Calculate duration based on granule position

	if lastGranule > 0 {

		// Formula for duration: (lastGranule - preSkip) / sampleRate

		durationSeconds := float64(lastGranule-uint64(preSkip)) / float64(sampleRate)

		duration = uint32(math.Ceil(durationSeconds))

		fmt.Printf("Calculated Opus duration from granule: %f seconds (lastGranule=%d)\n",

			durationSeconds, lastGranule)

	} else {

		// Fallback to rough estimation if granule position not found

		fmt.Println("Warning: No valid granule position found, using estimation")

		durationEstimate := float64(len(data)) / 2000.0 // Very rough approximation

		duration = uint32(durationEstimate)

	}



	// Make sure we have a reasonable duration (at least 1 second, at most 300 seconds)

	if duration < 1 {

		duration = 1

	} else if duration > 300 {

		duration = 300

	}



	// Generate waveform

	waveform = placeholderWaveform(duration)



	fmt.Printf("Ogg Opus analysis: size=%d bytes, calculated duration=%d sec, waveform=%d bytes\n",

		len(data), duration, len(waveform))



	return duration, waveform, nil

}



// min returns the smaller of x or y

func min(x, y int) int {

	if x < y {

		return x

	}

	return y

}



// placeholderWaveform generates a synthetic waveform for WhatsApp voice messages

// that appears natural with some variability based on the duration

func placeholderWaveform(duration uint32) []byte {

	// WhatsApp expects a 64-byte waveform for voice messages

	const waveformLength = 64

	waveform := make([]byte, waveformLength)



	// Seed the random number generator for consistent results with the same duration

	rand.Seed(int64(duration))



	// Create a more natural looking waveform with some patterns and variability

	// rather than completely random values



	// Base amplitude and frequency - longer messages get faster frequency

	baseAmplitude := 35.0

	frequencyFactor := float64(min(int(duration), 120)) / 30.0



	for i := range waveform {

		// Position in the waveform (normalized 0-1)

		pos := float64(i) / float64(waveformLength)



		// Create a wave pattern with some randomness

		// Use multiple sine waves of different frequencies for more natural look

		val := baseAmplitude * math.Sin(pos*math.Pi*frequencyFactor*8)

		val += (baseAmplitude / 2) * math.Sin(pos*math.Pi*frequencyFactor*16)



		// Add some randomness to make it look more natural

		val += (rand.Float64() - 0.5) * 15



		// Add some fade-in and fade-out effects

		fadeInOut := math.Sin(pos * math.Pi)

		val = val * (0.7 + 0.3*fadeInOut)



		// Center around 50 (typical voice baseline)

		val = val + 50



		// Ensure values stay within WhatsApp's expected range (0-100)

		if val < 0 {

			val = 0

		} else if val > 100 {

			val = 100

		}



		waveform[i] = byte(val)

	}



	return waveform

}



