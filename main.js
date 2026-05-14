const http = require("http");
const fs = require("fs");
const path = require("path");
const crypto = require('crypto');
const Busboy = require("busboy");
const {
	generateRegistrationOptions,
	verifyRegistrationResponse,
	generateAuthenticationOptions,
	verifyAuthenticationResponse,
} = require("@simplewebauthn/server");

const ROOT_DIR = __dirname;
const CONFIG_PATH = path.join(ROOT_DIR, "config.json");
const DATA_DIR = path.join(ROOT_DIR, "data");
const FILES_DIR = path.join(DATA_DIR, "files");
const TEXTS_DIR = path.join(DATA_DIR, "texts");
const INDEX_PATH = path.join(DATA_DIR, "index.json");
const WEBAUTHN_PATH = path.join(DATA_DIR, "webauthn.json");
const LOGS_DIR = path.join(ROOT_DIR, "logs");

const ONE_HOUR_MS = 60 * 60 * 1000;
const CLEANUP_INTERVAL_MS = 60 * 1000;
const TOKEN_TTL_MS = 60 * 1000;

let config = { password: "", sizeLimit: 0 };
let items = [];
let webauthnStore = { users: [] };
const uploadTokens = new Map();
const webauthnChallenges = new Map();

function ensureDir(dirPath) {
	if (!fs.existsSync(dirPath)) {
		fs.mkdirSync(dirPath, { recursive: true });
	}
}

function readConfig() {
	const raw = fs.readFileSync(CONFIG_PATH, "utf8");
	const parsed = JSON.parse(raw);
	config = {
		password: String(parsed.password || ""),
		sizeLimit: Number(parsed.sizeLimit || 0),
		addWebAuthn: Boolean(parsed.addWebAuthn),
	};
}

function loadWebAuthnStore() {
	if (!fs.existsSync(WEBAUTHN_PATH)) {
		webauthnStore = { users: [] };
		saveWebAuthnStore();
		return;
	}
	const raw = fs.readFileSync(WEBAUTHN_PATH, "utf8");
	const parsed = JSON.parse(raw);
	webauthnStore = parsed && Array.isArray(parsed.users) ? parsed : { users: [] };
	normalizeWebAuthnStore();
}

function saveWebAuthnStore() {
	const tmpPath = `${WEBAUTHN_PATH}.tmp`;
	fs.writeFileSync(tmpPath, JSON.stringify(webauthnStore, null, 2), "utf8");
	fs.renameSync(tmpPath, WEBAUTHN_PATH);
}

function loadIndex() {
	if (!fs.existsSync(INDEX_PATH)) {
		items = [];
		return;
	}
	const raw = fs.readFileSync(INDEX_PATH, "utf8");
	const parsed = JSON.parse(raw);
	items = Array.isArray(parsed) ? parsed : [];
}

function saveIndex() {
	const tmpPath = `${INDEX_PATH}.tmp`;
	fs.writeFileSync(tmpPath, JSON.stringify(items, null, 2), "utf8");
	fs.renameSync(tmpPath, INDEX_PATH);
}

function pad2(value) {
	return String(value).padStart(2, "0");
}

function getLocalDateInfo(date = new Date()) {
	return {
		year: date.getFullYear(),
		month: pad2(date.getMonth() + 1),
		day: pad2(date.getDate()),
		hour: pad2(date.getHours()),
		minute: pad2(date.getMinutes()),
		second: pad2(date.getSeconds()),
	};
}

function getLogFilePath(date = new Date()) {
	const info = getLocalDateInfo(date);
	return path.join(LOGS_DIR, `${info.year}-${info.month}-${info.day}.log`);
}

function getTimestamp(date = new Date()) {
	const info = getLocalDateInfo(date);
	return `${info.year}-${info.month}-${info.day} ${info.hour}:${info.minute}:${info.second}`;
}

function getClientIp(req) {
	const forwarded = req.headers["x-forwarded-for"];
	if (forwarded && typeof forwarded === "string") {
		return forwarded.split(",")[0].trim();
	}
	return req.socket.remoteAddress || "unknown";
}

function writeLog(req, action, detail) {
	const line = `${getTimestamp()} | ${getClientIp(req)} | ${action} | ${detail}`;
	const logPath = getLogFilePath();
	fs.appendFile(logPath, `${line}\n`, () => undefined);
}

function createId() {
	return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
}

function createToken() {
	return `${createId()}-${Math.random().toString(36).slice(2, 10)}`;
}

function decodeUploadFilename(rawName) {
	if (!rawName) return "";
	try {
		return Buffer.from(String(rawName), "latin1").toString("utf8");
	} catch (err) {
		return String(rawName);
	}
}

function bufferToBase64Url(buffer) {
	return Buffer.from(buffer)
		.toString("base64")
		.replace(/\+/g, "-")
		.replace(/\//g, "_")
		.replace(/=+$/g, "");
}

function base64UrlToBuffer(value) {
	const base64 = String(value).replace(/-/g, "+").replace(/_/g, "/");
	const padLength = (4 - (base64.length % 4)) % 4;
	const padded = `${base64}${"=".repeat(padLength)}`;
	return Buffer.from(padded, "base64");
}

function isBase64Url(value) {
	return /^[A-Za-z0-9_-]+$/.test(value);
}

function normalizeCredentialIdValue(value) {
	if (!value) return "";
	if (Buffer.isBuffer(value) || value instanceof Uint8Array) {
		return bufferToBase64Url(Buffer.from(value));
	}
	if (typeof value !== "string") return "";
	if (!isBase64Url(value)) {
		return bufferToBase64Url(Buffer.from(value, "utf8"));
	}
	const decoded = base64UrlToBuffer(value).toString("utf8");
	if (isBase64Url(decoded)) {
		return bufferToBase64Url(base64UrlToBuffer(decoded));
	}
	return bufferToBase64Url(base64UrlToBuffer(value));
}

function normalizeWebAuthnStore() {
	let changed = false;
	webauthnStore.users.forEach((user) => {
		user.credentials.forEach((cred) => {
			const normalized = normalizeCredentialIdValue(cred.id);
			if (normalized && normalized !== cred.id) {
				cred.id = normalized;
				changed = true;
			}
		});
	});
	if (changed) {
		saveWebAuthnStore();
	}
}

function getForwardedHost(req) {
	const forwardedHost = req.headers["x-forwarded-host"];
	const host = forwardedHost ? String(forwardedHost).split(",")[0].trim() : req.headers.host;
	return host || "localhost";
}

function getOriginHeader(req) {
	const origin = req.headers.origin;
	return typeof origin === "string" && origin.startsWith("http") ? origin : "";
}

function getRpId(req) {
	const origin = getOriginHeader(req);
	if (origin) {
		try {
			return new URL(origin).hostname;
		} catch (err) {
			return getForwardedHost(req).split(":")[0];
		}
	}
	return getForwardedHost(req).split(":")[0];
}

function getOrigin(req) {
	const origin = getOriginHeader(req);
	if (origin) return origin;
	const forwardedProto = req.headers["x-forwarded-proto"];
	const proto = forwardedProto ? String(forwardedProto).split(",")[0].trim() : "http";
	return `${proto}://${getForwardedHost(req)}`;
}

function getUserByUsername(username) {
	return webauthnStore.users.find((user) => user.username === username) || null;
}

function getUserById(id) {
	return webauthnStore.users.find((user) => user.id === id) || null;
}

function getCredentialById(credentialId) {
	for (const user of webauthnStore.users) {
		const found = user.credentials.find((cred) => cred.id === credentialId);
		if (found) return { user, credential: found };
	}
	return null;
}

function ensureWebAuthnEnabled(res) {
	if (!config.addWebAuthn) {
		sendJson(res, 403, { error: "未启用通行密钥" });
		return false;
	}
	return true;
}

function pruneTokens() {
	const now = Date.now();
	for (const [token, expiresAt] of uploadTokens.entries()) {
		if (expiresAt <= now) {
			uploadTokens.delete(token);
		}
	}
}

function getUploadToken(req) {
	const header = req.headers["x-upload-token"];
	if (header && typeof header === "string") return header.trim();
	const auth = req.headers.authorization;
	if (auth && typeof auth === "string" && auth.startsWith("Bearer ")) {
		return auth.slice(7).trim();
	}
	return "";
}

function getItemById(id) {
	return items.find((item) => item.id === id);
}

function removeItemById(id) {
	const idx = items.findIndex((item) => item.id === id);
	if (idx === -1) return null;
	const [removed] = items.splice(idx, 1);
	return removed;
}

function cleanupExpired(reason) {
	const now = Date.now();
	const expired = items.filter((item) => item.expiresAt <= now);
	if (expired.length === 0) return;
	expired.forEach((item) => {
		if (item.type === "file" && item.storageName) {
			fs.rm(path.join(FILES_DIR, item.storageName), { force: true }, () => undefined);
		}
		if (item.type === "text" && item.storageName) {
			fs.rm(path.join(TEXTS_DIR, item.storageName), { force: true }, () => undefined);
		}
		writeLog({ headers: {}, socket: { remoteAddress: "system" } }, reason, `${item.type}:${item.name}`);
	});
	items = items.filter((item) => item.expiresAt > now);
	saveIndex();
}

function scheduleDailyCleanup() {
	const now = new Date();
	const next = new Date(now);
	next.setHours(4, 0, 0, 0);
	if (next <= now) {
		next.setDate(next.getDate() + 1);
	}
	const delay = next.getTime() - now.getTime();
	setTimeout(() => {
		items.forEach((item) => {
			if (item.type === "file" && item.storageName) {
				fs.rm(path.join(FILES_DIR, item.storageName), { force: true }, () => undefined);
			}
			if (item.type === "text" && item.storageName) {
				fs.rm(path.join(TEXTS_DIR, item.storageName), { force: true }, () => undefined);
			}
		});
		const count = items.length;
		items = [];
		saveIndex();
		writeLog({ headers: {}, socket: { remoteAddress: "system" } }, "daily-clear", `${count} items`);
		scheduleDailyCleanup();
	}, delay);
}

function sendJson(res, statusCode, payload) {
	const body = JSON.stringify(payload);
	res.writeHead(statusCode, {
		"Content-Type": "application/json; charset=utf-8",
		"Content-Length": Buffer.byteLength(body),
	});
	res.end(body);
}

function sendText(res, statusCode, body) {
	res.writeHead(statusCode, {
		"Content-Type": "text/plain; charset=utf-8",
		"Content-Length": Buffer.byteLength(body),
	});
	res.end(body);
}

function serveFile(res, filePath, contentType) {
	fs.readFile(filePath, (err, data) => {
		if (err) {
			sendText(res, 404, "未找到");
			return;
		}
		res.writeHead(200, {
			"Content-Type": contentType,
			"Content-Length": data.length,
		});
		res.end(data);
	});
}

function getContentType(filePath) {
	const ext = path.extname(filePath).toLowerCase();
	switch (ext) {
		case ".html":
			return "text/html; charset=utf-8";
		case ".css":
			return "text/css; charset=utf-8";
		case ".js":
			return "text/javascript; charset=utf-8";
		case ".svg":
			return "image/svg+xml";
		case ".json":
			return "application/json; charset=utf-8";
		case ".png":
			return "image/png";
		case ".jpg":
		case ".jpeg":
			return "image/jpeg";
		default:
			return "application/octet-stream";
	}
}

function parseJsonBody(req, limitBytes) {
	return new Promise((resolve, reject) => {
		const chunks = [];
		let total = 0;
		req.on("data", (chunk) => {
			total += chunk.length;
			if (total > limitBytes) {
				reject(new Error("Payload too large"));
				req.destroy();
				return;
			}
			chunks.push(chunk);
		});
		req.on("end", () => {
			try {
				const parsed = JSON.parse(Buffer.concat(chunks).toString("utf8"));
				resolve(parsed);
			} catch (err) {
				reject(err);
			}
		});
		req.on("error", reject);
	});
}

function formatNameFromText(text) {
	const trimmed = text.trim();
	if (!trimmed) return "文本";
	const line = trimmed.split("\n")[0].trim();
	const preview = line.slice(0, 30);
	return preview || "文本";
}

ensureDir(DATA_DIR);
ensureDir(FILES_DIR);
ensureDir(TEXTS_DIR);
ensureDir(LOGS_DIR);
readConfig();
loadIndex();
loadWebAuthnStore();
cleanupExpired("startup-expire");
setInterval(() => cleanupExpired("expire"), CLEANUP_INTERVAL_MS);
scheduleDailyCleanup();

const server = http.createServer(async (req, res) => {
	const parsedUrl = new URL(req.url, `http://${req.headers.host || "localhost"}`);
	const pathname = decodeURIComponent(parsedUrl.pathname || "/");

	if (req.method === "GET" && pathname === "/") {
		return serveFile(res, path.join(ROOT_DIR, "index.html"), "text/html; charset=utf-8");
	}

	if (req.method === "GET" && pathname.startsWith("/assets/")) {
		const assetPath = path.join(ROOT_DIR, pathname);
		if (!assetPath.startsWith(path.join(ROOT_DIR, "assets"))) {
			return sendText(res, 403, "禁止访问");
		}
		return serveFile(res, assetPath, getContentType(assetPath));
	}

	cleanupExpired("expire");

	if (req.method === "GET" && pathname === "/api/list") {
		const sorted = [...items].sort((a, b) => b.createdAt - a.createdAt);
		return sendJson(res, 200, {
			items: sorted,
			sizeLimit: config.sizeLimit,
			addWebAuthn: config.addWebAuthn,
		});
	}

	if (req.method === "POST" && pathname === "/api/auth") {
		try {
			const body = await parseJsonBody(req, 1024 * 64);
			const password = String(body.password || "");
			if (password !== config.password) {
				return sendJson(res, 401, { error: "密码错误" });
			}
			pruneTokens();
			const token = createToken();
			const expiresAt = Date.now() + TOKEN_TTL_MS;
			uploadTokens.set(token, expiresAt);
			return sendJson(res, 200, { token, expiresAt });
		} catch (err) {
			return sendJson(res, 400, { error: "请求无效" });
		}
	}

	if (req.method === "POST" && pathname === "/api/webauthn/register/options") {
		if (!ensureWebAuthnEnabled(res)) return;
		try {
			const body = await parseJsonBody(req, 1024 * 64);
			const username = String(body.username || "").trim();
			if (!username) {
				return sendJson(res, 400, { error: "请输入用户名" });
			}
			let user = getUserByUsername(username);
			if (!user) {
				user = {
					id: createId(),
					username,
					createdAt: Date.now(),
					updatedAt: Date.now(),
					credentials: [],
				};
				webauthnStore.users.push(user);
				saveWebAuthnStore();
			}
			const rpId = getRpId(req);
			const options = await generateRegistrationOptions({
				rpName: "临时文件仓库",
				rpID: rpId,
				userID: Buffer.from(user.id, "utf8"),
				userName: user.username,
				timeout: 60000,
				attestationType: "none",
				excludeCredentials: user.credentials.map((cred) => ({
					id: base64UrlToBuffer(cred.id),
					type: "public-key",
					transports: cred.transports || [],
				})),
			});
			const requestId = createToken();
			webauthnChallenges.set(requestId, {
				type: "register",
				challenge: options.challenge,
				username,
				createdAt: Date.now(),
			});
			return sendJson(res, 200, { options, requestId });
		} catch (err) {
			return sendJson(res, 400, { error: "请求无效" });
		}
	}

	if (req.method === "POST" && pathname === "/api/webauthn/register/verify") {
		if (!ensureWebAuthnEnabled(res)) return;
		try {
			const body = await parseJsonBody(req, 1024 * 256);
			const requestId = String(body.requestId || "");
			const response = body.response || null;
			if (!requestId || !response) {
				return sendJson(res, 400, { error: "请求无效" });
			}
			const record = webauthnChallenges.get(requestId);
			if (!record || record.type !== "register") {
				return sendJson(res, 400, { error: "请求已过期" });
			}
			webauthnChallenges.delete(requestId);
			const expectedOrigin = getOrigin(req);
			const expectedRPID = getRpId(req);
			const verification = await verifyRegistrationResponse({
				response,
				expectedChallenge: record.challenge,
				expectedOrigin,
				expectedRPID,
			});
			if (!verification.verified || !verification.registrationInfo) {
				return sendJson(res, 400, { error: "验证失败" });
			}
			const { credentialID, credentialPublicKey, counter } = verification.registrationInfo;
			const user = getUserByUsername(record.username);
			if (!user) {
				return sendJson(res, 400, { error: "用户不存在" });
			}
			const credentialId = normalizeCredentialIdValue(credentialID);
			const exists = user.credentials.some((cred) => cred.id === credentialId);
			if (!exists) {
				user.credentials.push({
					id: credentialId,
					publicKey: bufferToBase64Url(credentialPublicKey),
					counter,
					transports: response.response && response.response.transports ? response.response.transports : [],
					createdAt: Date.now(),
				});
				user.updatedAt = Date.now();
				saveWebAuthnStore();
			}
			writeLog(req, "webauthn-register", `${record.username}`);
			return sendJson(res, 200, { ok: true });
		} catch (err) {
			console.error("webauthn register verify failed", err);
			return sendJson(res, 400, { error: "验证失败" });
		}
	}

	if (req.method === "POST" && pathname === "/api/webauthn/auth/options") {
		try {
			const body = await parseJsonBody(req, 1024 * 64);
			const username = String(body.username || "").trim();
			let allowCredentials = [];
			if (username) {
				const user = getUserByUsername(username);
				if (!user || user.credentials.length === 0) {
					return sendJson(res, 404, { error: "未找到通行密钥" });
				}
				allowCredentials = user.credentials.map((cred) => ({
					id: base64UrlToBuffer(cred.id),
					type: "public-key",
					transports: cred.transports || [],
				}));
			}
			const rpId = getRpId(req);
			const options = await generateAuthenticationOptions({
				rpID: rpId,
				allowCredentials,
				userVerification: "preferred",
				timeout: 60000,
			});
			const requestId = createToken();
			webauthnChallenges.set(requestId, {
				type: "auth",
				challenge: options.challenge,
				username: username || "",
				createdAt: Date.now(),
			});
			return sendJson(res, 200, { options, requestId });
		} catch (err) {
			return sendJson(res, 400, { error: "请求无效" });
		}
	}

	if (req.method === "POST" && pathname === "/api/webauthn/auth/verify") {
		try {
			const body = await parseJsonBody(req, 1024 * 256);
			const requestId = String(body.requestId || "");
			const response = body.response || null;
			if (!requestId || !response) {
				return sendJson(res, 400, { error: "请求无效" });
			}
			const record = webauthnChallenges.get(requestId);
			if (!record || record.type !== "auth") {
				return sendJson(res, 400, { error: "请求已过期" });
			}
			webauthnChallenges.delete(requestId);
			const credentialId = normalizeCredentialIdValue(response.rawId || response.id || "");
			const matched = record.username
				? (() => {
					const user = getUserByUsername(record.username);
					if (!user) return null;
					const credential = user.credentials.find((cred) => cred.id === credentialId);
					return credential ? { user, credential } : null;
				})()
				: getCredentialById(credentialId);
			if (!matched) {
				return sendJson(res, 404, { error: "未找到通行密钥" });
			}
			const expectedOrigin = getOrigin(req);
			const expectedRPID = getRpId(req);
			const verification = await verifyAuthenticationResponse({
				response,
				expectedChallenge: record.challenge,
				expectedOrigin,
				expectedRPID,
				authenticator: {
					credentialID: base64UrlToBuffer(matched.credential.id),
					credentialPublicKey: base64UrlToBuffer(matched.credential.publicKey),
					counter: matched.credential.counter,
					transports: matched.credential.transports || [],
				},
			});
			if (!verification.verified) {
				return sendJson(res, 401, { error: "验证失败" });
			}
			matched.credential.counter = verification.authenticationInfo.newCounter;
			matched.user.updatedAt = Date.now();
			saveWebAuthnStore();
			pruneTokens();
			const token = createToken();
			const expiresAt = Date.now() + TOKEN_TTL_MS;
			uploadTokens.set(token, expiresAt);
			writeLog(req, "webauthn-auth", `${matched.user.username}`);
			return sendJson(res, 200, { token, expiresAt });
		} catch (err) {
			console.error("webauthn auth verify failed", err);
			return sendJson(res, 400, { error: "验证失败" });
		}
	}

	if (req.method === "GET" && pathname === "/api/webauthn/credentials") {
		pruneTokens();
		const token = getUploadToken(req);
		const tokenExpiry = token ? uploadTokens.get(token) : null;
		if (!tokenExpiry || tokenExpiry <= Date.now()) {
			return sendJson(res, 401, { error: "令牌无效或已过期" });
		}
		const credentials = webauthnStore.users.flatMap((user) =>
			user.credentials.map((cred) => ({
				id: cred.id,
				username: user.username,
				createdAt: cred.createdAt,
				transports: cred.transports || [],
			}))
		);
		return sendJson(res, 200, { credentials });
	}

	if (req.method === "DELETE" && pathname.startsWith("/api/webauthn/credential/")) {
		pruneTokens();
		const token = getUploadToken(req);
		const tokenExpiry = token ? uploadTokens.get(token) : null;
		if (!tokenExpiry || tokenExpiry <= Date.now()) {
			return sendJson(res, 401, { error: "令牌无效或已过期" });
		}
		const credentialId = pathname.split("/").pop();
		const matched = getCredentialById(credentialId);
		if (!matched) {
			return sendJson(res, 404, { error: "未找到通行密钥" });
		}
		matched.user.credentials = matched.user.credentials.filter((cred) => cred.id !== credentialId);
		if (matched.user.credentials.length === 0) {
			webauthnStore.users = webauthnStore.users.filter((user) => user.id !== matched.user.id);
		}
		saveWebAuthnStore();
		writeLog(req, "webauthn-delete", `${matched.user.username}`);
		return sendJson(res, 200, { ok: true });
	}

	if (req.method === "POST" && pathname === "/api/upload") {
		pruneTokens();
		const token = getUploadToken(req);
		const tokenExpiry = token ? uploadTokens.get(token) : null;
		if (!tokenExpiry || tokenExpiry <= Date.now()) {
			sendJson(res, 401, { error: "令牌无效或已过期" });
			req.destroy();
			return;
		}
		const limits = { files: 1 };
		if (config.sizeLimit > 0) {
			limits.fileSize = config.sizeLimit;
		}
		const busboy = Busboy({
			headers: req.headers,
			limits,
		});
		let fileHandled = false;
		let fileTooLarge = false;
		let pendingFile = null;
		let fileDoneResolve = null;
		const fileDone = new Promise((resolve) => {
			fileDoneResolve = resolve;
		});
		let hasErrored = false;

		busboy.on("file", (fieldname, file, info) => {
			if (fieldname !== "file") {
				file.resume();
				return;
			}
			fileHandled = true;
			const rawName = typeof info === "object" ? info.filename : String(info || "");
			const originalName = decodeUploadFilename(rawName);
			const id = crypto.createHash('sha256').update(createId()).digest('hex');
			const ext = path.extname(originalName || "");
			const storageName = id;
			const storagePath = path.join(FILES_DIR, storageName);
			const writeStream = fs.createWriteStream(storagePath);
			let total = 0;

			file.on("data", (chunk) => {
				total += chunk.length;
			});

			file.on("limit", () => {
				fileTooLarge = true;
			});

			file.on("error", () => {
				hasErrored = true;
				fileDoneResolve();
			});

			writeStream.on("error", () => {
				hasErrored = true;
				fileDoneResolve();
			});

			file.pipe(writeStream);

			writeStream.on("close", () => {
				pendingFile = {
					id,
					name: originalName || "文件",
					storageName,
					size: total,
					storagePath,
				};
				fileDoneResolve();
			});
		});

		busboy.on("error", () => {
			hasErrored = true;
			if (!res.headersSent) {
				sendJson(res, 400, { error: "上传失败" });
			}
		});

		busboy.on("finish", async () => {
			if (!fileHandled) {
				return sendJson(res, 400, { error: "未选择文件" });
			}
			await fileDone;
			if (res.headersSent) {
				return;
			}
			if (hasErrored) {
				if (pendingFile && pendingFile.storagePath) {
					fs.rm(pendingFile.storagePath, { force: true }, () => undefined);
				}
				return sendJson(res, 400, { error: "上传失败" });
			}
			if (fileTooLarge) {
				if (pendingFile && pendingFile.storagePath) {
					fs.rm(pendingFile.storagePath, { force: true }, () => undefined);
				}
				return sendJson(res, 413, { error: "文件过大" });
			}
			if (!pendingFile) {
				return sendJson(res, 500, { error: "上传失败" });
			}
			const now = Date.now();
			const savedItem = {
				id: pendingFile.id,
				type: "file",
				name: pendingFile.name,
				storageName: pendingFile.storageName,
				size: pendingFile.size,
				createdAt: now,
				expiresAt: now + ONE_HOUR_MS,
			};
			items.push(savedItem);
			saveIndex();
			writeLog(req, "upload", `${savedItem.name}`);
			return sendJson(res, 200, { ok: true, item: savedItem });
		});

		req.pipe(busboy);
		return;
	}

	if (req.method === "POST" && pathname === "/api/text") {
		try {
			pruneTokens();
			const token = getUploadToken(req);
			const tokenExpiry = token ? uploadTokens.get(token) : null;
			if (!tokenExpiry || tokenExpiry <= Date.now()) {
				return sendJson(res, 401, { error: "令牌无效或已过期" });
			}
			const limitBytes = config.sizeLimit > 0 ? config.sizeLimit : 10 * 1024 * 1024;
			const body = await parseJsonBody(req, limitBytes);
			const text = String(body.text || "");
			const size = Buffer.byteLength(text, "utf8");
			if (!text.trim()) {
				return sendJson(res, 400, { error: "文本为空" });
			}
			if (config.sizeLimit && size > config.sizeLimit) {
				return sendJson(res, 413, { error: "文本过大" });
			}
			const id = createId();
			const storageName = `${id}.txt`;
			const storagePath = path.join(TEXTS_DIR, storageName);
			fs.writeFileSync(storagePath, text, "utf8");
			const now = Date.now();
			const item = {
				id,
				type: "text",
				name: formatNameFromText(text),
				storageName,
				size,
				createdAt: now,
				expiresAt: now + ONE_HOUR_MS,
			};
			items.push(item);
			saveIndex();
			writeLog(req, "text-upload", `${item.name}`);
			return sendJson(res, 200, { ok: true, item });
		} catch (err) {
			return sendJson(res, 400, { error: "请求无效" });
		}
	}

	if (req.method === "GET" && pathname.startsWith("/api/download/")) {
		const id = pathname.split("/").pop();
		const item = getItemById(id);
		if (!item || item.type !== "file") {
			return sendText(res, 404, "未找到");
		}
		const filePath = path.join(FILES_DIR, item.storageName);
		fs.stat(filePath, (err, stat) => {
			if (err) {
				return sendText(res, 404, "未找到");
			}
			res.writeHead(200, {
				"Content-Type": "application/octet-stream",
				"Content-Disposition": `attachment; filename*=UTF-8''${encodeURIComponent(item.name)}`,
				"Content-Length": stat.size,
			});
			const stream = fs.createReadStream(filePath);
			stream.pipe(res);
			writeLog(req, "download", `${item.name}`);
		});
		return;
	}

	if (req.method === "GET" && pathname.startsWith("/api/text/")) {
		const id = pathname.split("/").pop();
		const item = getItemById(id);
		if (!item || item.type !== "text") {
			return sendText(res, 404, "未找到");
		}
		const filePath = path.join(TEXTS_DIR, item.storageName);
		fs.readFile(filePath, "utf8", (err, data) => {
			if (err) {
				return sendText(res, 404, "未找到");
			}
			res.writeHead(200, {
				"Content-Type": "text/plain; charset=utf-8",
				"Content-Length": Buffer.byteLength(data),
			});
			res.end(data);
		});
		return;
	}

	if (req.method === "DELETE" && pathname.startsWith("/api/item/")) {
		const id = pathname.split("/").pop();
		const item = removeItemById(id);
		if (!item) {
			return sendJson(res, 404, { error: "未找到" });
		}
		if (item.type === "file" && item.storageName) {
			fs.rm(path.join(FILES_DIR, item.storageName), { force: true }, () => undefined);
		}
		if (item.type === "text" && item.storageName) {
			fs.rm(path.join(TEXTS_DIR, item.storageName), { force: true }, () => undefined);
		}
		saveIndex();
		writeLog(req, "delete", `${item.type}:${item.name}`);
		return sendJson(res, 200, { ok: true });
	}

	sendText(res, 404, "未找到");
});

server.listen(8489, () => {
	console.log("Temporary file store running at http://localhost:8489");
});
