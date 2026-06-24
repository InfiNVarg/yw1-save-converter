// ═══════════════════════════════════════════════════════════════════════════
// YW1 Save Converter — 3DS → Switch  (converter.js)
// Exact port of converter.py / ywsave.py to JavaScript
// ═══════════════════════════════════════════════════════════════════════════

// --- 1. CRC32 (same as zlib.crc32) ---
const _crc32Table = new Uint32Array(256);
for (let i = 0; i < 256; i++) {
    let c = i;
    for (let j = 0; j < 8; j++) {
        c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    }
    _crc32Table[i] = c;
}

function crc32(data) {
    let crc = 0xFFFFFFFF;
    for (let i = 0; i < data.length; i++) {
        crc = _crc32Table[(crc ^ data[i]) & 0xFF] ^ (crc >>> 8);
    }
    return (crc ^ 0xFFFFFFFF) >>> 0;
}

// --- 2. Xorshift128 (exact port of _Xorshift from ywsave.py) ---
class Xorshift {
    constructor(seed) {
        this.state = new Uint32Array(4);
        if (seed === 0) return;
        let s = seed >>> 0;
        s = (s ^ (s >>> 30)) >>> 0;
        s = (Math.imul(s, 0x6C078965)) >>> 0;
        s = (s + 1) >>> 0;
        this.state[0] = s;
        s = (s ^ (s >>> 30)) >>> 0;
        s = (Math.imul(s, 0x6C078965)) >>> 0;
        s = (s + 2) >>> 0;
        this.state[1] = s;
        s = (s ^ (s >>> 30)) >>> 0;
        s = (Math.imul(s, 0x6C078965)) >>> 0;
        s = (s + 3) >>> 0;
        this.state[2] = s;
        this.state[3] = 0x03DF95B3;
    }
    next(divisor = 0) {
        let s0 = this.state[0], s1 = this.state[1], s2 = this.state[2], s3 = this.state[3];
        let t = (s0 ^ (s0 << 11)) >>> 0;
        let s3n = ((s3 ^ (s3 >>> 19)) ^ (t ^ (t >>> 8))) >>> 0;
        this.state[0] = s1;
        this.state[1] = s2;
        this.state[2] = s3;
        this.state[3] = s3n;
        return divisor > 0 ? (s3n % (divisor >>> 0)) >>> 0 : s3n;
    }
}

// --- 3. YWCipher (exact port of YWCipher from ywsave.py) ---
const _ODD_PRIMES = [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
    61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
    139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
    229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
    317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
    421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
    521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617,
    619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727,
    733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829,
    839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947,
    953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051,
    1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
    1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289,
    1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427,
    1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523,
    1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621
];

class YWCipher {
    constructor(seed, count = 0x1000) {
        let prng = new Xorshift(seed);
        this.table = new Uint8Array(256);
        for (let i = 0; i < 256; i++) this.table[i] = i;
        for (let i = 0; i < count; i++) {
            let r = prng.next(0x10000);
            let r1 = r & 0xFF;
            let r2 = (r >>> 8) & 0xFF;
            if (r1 !== r2) {
                // CRITICAL: indirect swap — i1=table[r1], i2=table[r2], swap table[i1]↔table[i2]
                let i1 = this.table[r1];
                let i2 = this.table[r2];
                let temp = this.table[i1];
                this.table[i1] = this.table[i2];
                this.table[i2] = temp;
            }
        }
    }
    crypt(data) {
        let out = new Uint8Array(data.length);
        let ka = 0;
        for (let idx = 0; idx < data.length; idx++) {
            if (idx % 0x100 === 0) {
                ka = _ODD_PRIMES[this.table[(idx & 0xFF00) >>> 8]];
            }
            let kb = this.table[(ka * (idx + 1)) & 0xFF];
            out[idx] = data[idx] ^ kb;
        }
        return out;
    }
}

// --- 4. Section tree parser (exact port of parse_sections) ---
class Section {
    constructor(id, offset, size, parent = null) {
        this.id = id;
        this.offset = offset;
        this.size = size;
        this.parent = parent;
        this.children = [];
    }
    find(id) {
        if (this.id === id) return this;
        for (let child of this.children) {
            let res = child.find(id);
            if (res) return res;
        }
        return null;
    }
}

function parseSections(plain) {
    let dv = new DataView(plain.buffer, plain.byteOffset, plain.byteLength);
    let n = plain.length;
    function u32(p) { return dv.getUint32(p, true); }

    let pos = 0;
    let h1 = u32(pos); pos += 4;
    if ((h1 & 0xFFFF) !== 0xFFFE) {
        throw new Error("Cabecera mágica 0xFFFE no encontrada (parse error)");
    }
    let h2 = u32(pos); pos += 4;
    let root = new Section(h2 & 0xFF, pos, h2 >>> 8, null);
    let stack = [root];

    while (pos < n) {
        let size = 4;
        h1 = u32(pos); pos += 4;
        while ((h1 & 0xFFFF) === 0xFFFE) {
            h2 = u32(pos); pos += 4;
            let sid = h2 & 0xFF;
            size = h2 >>> 8;
            if (stack.length === 0) throw new Error("parse error: pila vacía");
            if (pos + size > n) throw new Error("parse error: tamaño de sección inválido");
            let node = new Section(sid, pos, size, stack[stack.length - 1]);
            stack[stack.length - 1].children.push(node);
            stack.push(node);
            h1 = u32(pos); pos += 4;
        }
        if ((h1 & 0xFFFF) === 0xFEFF) {
            stack.pop();
        }
        pos += size - 4;
    }
    return root;
}

// --- 5. Load / Save raw save ---
function loadRawSave(buffer) {
    let bytes = new Uint8Array(buffer);
    if (bytes.length < 8) throw new Error("Archivo demasiado pequeño para ser un save de YW1");
    let dv = new DataView(buffer);
    let crcStored = dv.getUint32(bytes.length - 8, true);
    let key = dv.getUint32(bytes.length - 4, true);
    let payload = bytes.slice(0, bytes.length - 8);
    let actualCrc = crc32(payload);
    if (crcStored !== actualCrc) {
        throw new Error("CRC32 inválido. El archivo no es un save de YW1 válido o está corrupto.");
    }
    let cipher = new YWCipher(key);
    let plain = cipher.crypt(payload);
    let root = parseSections(plain);
    let sec7 = root.find(0x07);
    let yokaiEntrySize = sec7 ? Math.floor(sec7.size / 241) : 0x5C;
    let platform = yokaiEntrySize > 0x5C ? "Switch" : "3DS";
    return { plain, key, root, platform, yokaiEntrySize };
}

function saveRawSave(plain, key) {
    let cipher = new YWCipher(key);
    let encrypted = cipher.crypt(plain);
    let crcVal = crc32(encrypted);
    let out = new Uint8Array(encrypted.length + 8);
    out.set(encrypted, 0);
    let dv = new DataView(out.buffer);
    dv.setUint32(encrypted.length, crcVal, true);
    dv.setUint32(encrypted.length + 4, key, true);
    return out;
}

// --- 6. Conversion logic (exact port of convert_3ds_to_switch) ---
const YOKAI_SLOTS = 241;
const COPY_SECTIONS = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x08, 0x09, 0x0A, 0x0D, 0x0E, 0x0F, 0x10];
const EXPAND_SECTIONS = [0x0B, 0x0C];

function convert3dsToSwitch(sv3ds, svSwitch, logFn) {
    if (sv3ds.platform !== '3DS') throw new Error('El primer archivo debe ser un save de 3DS.');
    if (svSwitch.platform !== 'Switch') throw new Error('El segundo archivo debe ser un save plantilla de Switch.');

    let result = new Uint8Array(svSwitch.plain.length);
    result.set(svSwitch.plain);

    // 1) Copy identical-size sections
    logFn('Copiando secciones compatibles...');
    for (let sid of COPY_SECTIONS) {
        let src = sv3ds.root.find(sid);
        let dst = svSwitch.root.find(sid);
        if (!src || !dst) continue;
        if (src.size !== dst.size) {
            throw new Error(
                `Tamaño inesperado en sección 0x${sid.toString(16).toUpperCase()}: ` +
                `3DS=${src.size} bytes, Switch=${dst.size} bytes. ` +
                `El save de Switch puede ser de otra versión del juego.`
            );
        }
        result.set(sv3ds.plain.slice(src.offset, src.offset + src.size), dst.offset);
    }

    // 1.5) Expand sections (0x0B, 0x0C — Watch rank lives in 0x0C byte[1])
    logFn('Expandiendo secciones 0x0B y 0x0C (rango del Watch)...');
    for (let sid of EXPAND_SECTIONS) {
        let src = sv3ds.root.find(sid);
        let dst = svSwitch.root.find(sid);
        if (!src || !dst) continue;
        let copyLen = Math.min(src.size, dst.size);
        result.set(sv3ds.plain.slice(src.offset, src.offset + copyLen), dst.offset);
        if (sid === 0x0C && dst.size > 0xAB) {
            result[dst.offset + 0xAB] = svSwitch.plain[dst.offset + 0xAB];
        }
    }

    // 2) Convert section 7 (Yokai): expand 0x5C → 0x7C per entry
    logFn('Convirtiendo 241 Yo-kai (0x5C → 0x7C por entrada)...');
    let src7 = sv3ds.root.find(0x07);
    let dst7 = svSwitch.root.find(0x07);
    for (let i = 0; i < YOKAI_SLOTS; i++) {
        let srcOff = src7.offset + 0x5C * i;
        let dstOff = dst7.offset + 0x7C * i;
        result.set(sv3ds.plain.slice(srcOff, srcOff + 0x20), dstOff);
        result.set(new Uint8Array(0x20), dstOff + 0x20);
        result.set(sv3ds.plain.slice(srcOff + 0x20, srcOff + 0x5C), dstOff + 0x40);
    }

    // 3) Header section 0xF2
    logFn('Transfiriendo cabecera (nombre, posición, mapa, rango)...');
    let hdr3 = sv3ds.root.find(0xF2);
    let hdrS = svSwitch.root.find(0xF2);
    if (hdr3 && hdrS) {
        // Position data (first 0x18 bytes)
        result.set(sv3ds.plain.slice(hdr3.offset, hdr3.offset + 0x18), hdrS.offset);

        // Player name: 3DS ASCII @ 0x18 → Switch fullwidth UTF-8 @ 0x20
        let rawName = sv3ds.plain.slice(hdr3.offset + 0x18, hdr3.offset + 0x18 + 0x10);
        let nullIdx = rawName.indexOf(0);
        if (nullIdx >= 0) rawName = rawName.slice(0, nullIdx);
        let nameAscii = new TextDecoder('ascii').decode(rawName);

        let fwName = '';
        for (let ch of nameAscii) {
            let c = ch.charCodeAt(0);
            if (c >= 0x21 && c <= 0x7E) fwName += String.fromCharCode(c + 0xFEE0);
            else if (c === 0x20) fwName += String.fromCharCode(0x3000);
            else fwName += ch;
        }
        let nameBytes = new TextEncoder().encode(fwName);
        let nameField = new Uint8Array(0x30);
        nameField.set(nameBytes.slice(0, 0x2F));
        result.set(nameField, hdrS.offset + 0x20);

        // Map ID: 3DS @ 0x38 → Switch @ 0x60 (8 bytes)
        result.set(sv3ds.plain.slice(hdr3.offset + 0x38, hdr3.offset + 0x38 + 8), hdrS.offset + 0x60);

        // Watch Rank: 3DS @ 0x54 → Switch @ 0x14C
        result[hdrS.offset + 0x14C] = sv3ds.plain[hdr3.offset + 0x54];
    }

    // 4) Rebuild yokai registry (section 0x0A)
    logFn('Reconstruyendo registro de Yo-kai...');
    let resultRoot = parseSections(result);
    let newDst7 = resultRoot.find(0x07);
    let newReg = resultRoot.find(0x0A);
    if (newDst7 && newReg) {
        let rdv = new DataView(result.buffer, result.byteOffset, result.byteLength);
        for (let i = 0; i < YOKAI_SLOTS; i++) {
            let eOff = newDst7.offset + 0x7C * i;
            let n1 = rdv.getUint16(eOff, true);
            let n2 = rdv.getUint16(eOff + 2, true);
            rdv.setUint32(newReg.offset + 4 * i, (n2 << 16) | n1, true);
        }
    }

    // 5) Encrypt and package
    logFn('Cifrando y empaquetando save final...');
    let finalSave = saveRawSave(result, svSwitch.key);

    logFn('✅ ¡Conversión completada con éxito!');
    return finalSave;
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. UI & DOM Logic
// ═══════════════════════════════════════════════════════════════════════════

let file3ds = null;   // { buffer: ArrayBuffer, name: string, save: parsed }
let fileSwitch = null;

// --- DOM elements ---
const zone3ds = document.getElementById('zone3ds');
const zoneSwitch = document.getElementById('zoneSwitch');
const input3ds = document.getElementById('input3ds');
const inputSwitch = document.getElementById('inputSwitch');
const btnConvert = document.getElementById('btnConvert');
const convertHint = document.getElementById('convertHint');

const downloadSection = document.getElementById('downloadSection');
const btnDownload = document.getElementById('btnDownload');
const downloadSize = document.getElementById('downloadSize');
const errorSection = document.getElementById('errorSection');
const errorMessage = document.getElementById('errorMessage');
const btnRetry = document.getElementById('btnRetry');

// --- Utility ---
function formatSize(bytes) {
    if (bytes < 1024) return bytes + ' B';
    return (bytes / 1024).toFixed(1) + ' KB';
}



function checkReady() {
    let ready = file3ds && fileSwitch;
    btnConvert.disabled = !ready;
    if (ready) {
        convertHint.textContent = '¡Listo para convertir!';
        convertHint.classList.add('ready');
    } else {
        convertHint.textContent = 'Carga ambos archivos para comenzar';
        convertHint.classList.remove('ready');
    }
}

// --- Drop zone helpers ---
function setupDropZone(zoneEl, inputEl, side) {
    // Click to browse
    zoneEl.addEventListener('click', (e) => {
        if (e.target.classList.contains('file-remove')) return;
        inputEl.click();
    });
    zoneEl.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); inputEl.click(); }
    });

    // File input change
    inputEl.addEventListener('change', () => {
        if (inputEl.files.length > 0) handleFile(inputEl.files[0], side);
    });

    // Drag events
    zoneEl.addEventListener('dragover', (e) => { e.preventDefault(); zoneEl.classList.add('dragover'); });
    zoneEl.addEventListener('dragleave', () => { zoneEl.classList.remove('dragover'); });
    zoneEl.addEventListener('drop', (e) => {
        e.preventDefault();
        zoneEl.classList.remove('dragover');
        if (e.dataTransfer.files.length > 0) handleFile(e.dataTransfer.files[0], side);
    });

    // Remove button
    let removeBtn = document.getElementById('zone' + (side === '3ds' ? '3ds' : 'Switch') + '-remove');
    removeBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        if (side === '3ds') file3ds = null; else fileSwitch = null;
        showZoneDefault(side);
        checkReady();
        // Reset sections
        downloadSection.hidden = true;
        errorSection.hidden = true;
    });
}

function showZoneDefault(side) {
    let prefix = side === '3ds' ? 'zone3ds' : 'zoneSwitch';
    document.getElementById(prefix + '-content').hidden = false;
    document.getElementById(prefix + '-info').hidden = true;
    let zoneEl = document.getElementById(prefix);
    zoneEl.classList.remove('loaded', 'error');
    
    let jibanyanEl = document.getElementById(side === '3ds' ? 'jibanyan3ds' : 'jibanyanSwitch');
    if (jibanyanEl) jibanyanEl.hidden = true;
}

function showZoneLoaded(side, fileName, fileSize, platform) {
    let prefix = side === '3ds' ? 'zone3ds' : 'zoneSwitch';
    document.getElementById(prefix + '-content').hidden = true;
    document.getElementById(prefix + '-info').hidden = false;
    document.getElementById(prefix + '-name').textContent = fileName;
    document.getElementById(prefix + '-size').textContent = formatSize(fileSize);
    document.getElementById(prefix + '-platform').textContent = 'Plataforma: ' + platform;
    let zoneEl = document.getElementById(prefix);
    zoneEl.classList.add('loaded');
    zoneEl.classList.remove('error');

    let jibanyanEl = document.getElementById(side === '3ds' ? 'jibanyan3ds' : 'jibanyanSwitch');
    if (jibanyanEl) jibanyanEl.hidden = false;
}

function showZoneError(side, msg) {
    let prefix = side === '3ds' ? 'zone3ds' : 'zoneSwitch';
    document.getElementById(prefix + '-content').hidden = true;
    document.getElementById(prefix + '-info').hidden = false;
    document.getElementById(prefix + '-name').textContent = 'Error';
    document.getElementById(prefix + '-size').textContent = msg;
    document.getElementById(prefix + '-platform').textContent = '';
    let zoneEl = document.getElementById(prefix);
    zoneEl.classList.add('error');
    zoneEl.classList.remove('loaded');

    let jibanyanEl = document.getElementById(side === '3ds' ? 'jibanyan3ds' : 'jibanyanSwitch');
    if (jibanyanEl) jibanyanEl.hidden = true;
}

function handleFile(file, side) {
    let reader = new FileReader();
    reader.onload = function() {
        try {
            let buffer = reader.result;
            let save = loadRawSave(buffer);
            if (side === '3ds') {
                if (save.platform !== '3DS') {
                    showZoneError(side, 'Este archivo no es un save de 3DS (detectado: ' + save.platform + ')');
                    file3ds = null;
                    checkReady();
                    return;
                }
                file3ds = { buffer, name: file.name, save };
            } else {
                if (save.platform !== 'Switch') {
                    showZoneError(side, 'Este archivo no es un save de Switch (detectado: ' + save.platform + ')');
                    fileSwitch = null;
                    checkReady();
                    return;
                }
                fileSwitch = { buffer, name: file.name, save };
            }
            showZoneLoaded(side, file.name, file.size, save.platform);
            checkReady();
        } catch (err) {
            showZoneError(side, err.message);
            if (side === '3ds') file3ds = null; else fileSwitch = null;
            checkReady();
        }
    };
    reader.readAsArrayBuffer(file);
}

// --- Convert ---
btnConvert.addEventListener('click', () => {
    downloadSection.hidden = true;
    errorSection.hidden = true;
    btnConvert.disabled = true;
    btnConvert.classList.add('converting');

    try {
        let result = convert3dsToSwitch(file3ds.save, fileSwitch.save, () => {});

        // Show download
        let blob = new Blob([result], { type: 'application/octet-stream' });
        let url = URL.createObjectURL(blob);
        btnDownload.href = url;
        downloadSize.textContent = formatSize(result.length);
        downloadSection.hidden = false;
        downloadSection.scrollIntoView({ behavior: 'smooth', block: 'nearest' });

    } catch (err) {
        errorMessage.textContent = err.message;
        errorSection.hidden = false;
        errorSection.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    } finally {
        btnConvert.disabled = false;
        btnConvert.classList.remove('converting');
    }
});

// --- Retry ---
btnRetry.addEventListener('click', () => {
    errorSection.hidden = true;
});

// --- Init ---
setupDropZone(zone3ds, input3ds, '3ds');
setupDropZone(zoneSwitch, inputSwitch, 'switch');
checkReady();

// --- Tutorial Collapsible ---
const btnOpenTutorial = document.getElementById('btnOpenTutorial');
const btnCloseTutorial = document.getElementById('btnCloseTutorial');
const tutorialCollapse = document.getElementById('tutorialCollapse');

if (btnOpenTutorial && btnCloseTutorial && tutorialCollapse) {
    const toggleTutorial = () => {
        const isHidden = tutorialCollapse.hidden;
        tutorialCollapse.hidden = !isHidden;
        if (!tutorialCollapse.hidden) {
            tutorialCollapse.scrollIntoView({ behavior: 'smooth', block: 'start' });
        }
    };

    btnOpenTutorial.addEventListener('click', toggleTutorial);
    btnCloseTutorial.addEventListener('click', () => {
        tutorialCollapse.hidden = true;
    });

    // Close on Escape key press
    window.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && !tutorialCollapse.hidden) {
            tutorialCollapse.hidden = true;
        }
    });
}

// --- Lightbox / Image Zoom ---
const lightboxOverlay = document.getElementById('lightboxOverlay');
const lightboxImg = document.getElementById('lightboxImg');
const btnLightboxClose = document.getElementById('btnLightboxClose');
const tutorialImages = document.querySelectorAll('.tutorial-img');

if (lightboxOverlay && lightboxImg && btnLightboxClose) {
    tutorialImages.forEach(img => {
        img.addEventListener('click', () => {
            lightboxImg.src = img.src;
            lightboxImg.alt = img.alt;
            lightboxOverlay.hidden = false;
        });
    });

    const closeLightbox = () => {
        lightboxOverlay.hidden = true;
        lightboxImg.src = '';
    };

    btnLightboxClose.addEventListener('click', closeLightbox);
    lightboxOverlay.addEventListener('click', (e) => {
        if (e.target === lightboxOverlay || e.target === lightboxImg.parentElement) {
            closeLightbox();
        }
    });

    window.addEventListener('keydown', (e) => {
        if (e.key === 'Escape' && !lightboxOverlay.hidden) {
            closeLightbox();
            e.stopPropagation();
        }
    }, true);
}
