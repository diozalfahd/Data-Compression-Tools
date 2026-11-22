
from flask import Flask, render_template, request, send_from_directory
from werkzeug.utils import secure_filename

import os
import time
import struct
import heapq
import io
import zipfile

from collections import Counter
from itertools import count


app = Flask(__name__)

UPLOAD_FOLDER = "uploads"
RESULT_FOLDER = "hasil"

os.makedirs(UPLOAD_FOLDER, exist_ok=True)
os.makedirs(RESULT_FOLDER, exist_ok=True)


# =====================================
# PENGATURAN
# =====================================

EKSTENSI = {
    "RLE": ".rle",
    "Huffman": ".huff",
    "LZ77": ".kres"
}


def normalisasi_algoritma(nilai):
    pemetaan = {
        "rle": "RLE",
        "huffman": "Huffman",
        "lz77": "LZ77"
    }

    return pemetaan.get((nilai or "").strip().lower())


# =====================================
# ALGORITMA RLE
# =====================================

def rle_compress(data):
    hasil = bytearray()
    i = 0

    while i < len(data):
        jumlah = 1

        while (
            i + jumlah < len(data)
            and data[i] == data[i + jumlah]
            and jumlah < 255
        ):
            jumlah += 1

        hasil.append(jumlah)
        hasil.append(data[i])
        i += jumlah

    return bytes(hasil)


def rle_decompress(data):
    if len(data) % 2 != 0:
        raise ValueError("Data RLE tidak valid")

    hasil = bytearray()

    for i in range(0, len(data), 2):
        jumlah = data[i]
        karakter = data[i + 1]

        if jumlah == 0:
            raise ValueError("Data RLE tidak valid")

        hasil.extend([karakter] * jumlah)

    return bytes(hasil)


# =====================================
# ALGORITMA HUFFMAN
# =====================================

def huffman_compress(data):
    frekuensi = Counter(data)
    tabel = [frekuensi.get(i, 0) for i in range(256)]

    if not data:
        return struct.pack(">256I", *tabel)

    antrian = []
    nomor = count()

    for karakter, jumlah in frekuensi.items():
        heapq.heappush(
            antrian,
            (jumlah, next(nomor), karakter)
        )

    while len(antrian) > 1:
        frek1, _, kiri = heapq.heappop(antrian)
        frek2, _, kanan = heapq.heappop(antrian)

        heapq.heappush(
            antrian,
            (frek1 + frek2, next(nomor), (kiri, kanan))
        )

    pohon = antrian[0][2]
    kode = {}

    def buat_kode(node, awalan=""):
        if isinstance(node, int):
            kode[node] = awalan or "0"
        else:
            buat_kode(node[0], awalan + "0")
            buat_kode(node[1], awalan + "1")

    buat_kode(pohon)

    bit = "".join(kode[karakter] for karakter in data)

    padding = (8 - len(bit) % 8) % 8
    bit += "0" * padding

    hasil = bytearray()

    for i in range(0, len(bit), 8):
        hasil.append(int(bit[i:i + 8], 2))

    return struct.pack(">256I", *tabel) + bytes(hasil)


def huffman_decompress(data, ukuran_asli):
    if len(data) < 1024:
        raise ValueError("Data Huffman tidak valid")

    tabel = struct.unpack(">256I", data[:1024])
    isi = data[1024:]

    if sum(tabel) != ukuran_asli:
        raise ValueError("Ukuran data Huffman tidak cocok")

    if ukuran_asli == 0:
        return b""

    antrian = []
    nomor = count()

    for karakter, jumlah in enumerate(tabel):
        if jumlah > 0:
            heapq.heappush(
                antrian,
                (jumlah, next(nomor), karakter)
            )

    if not antrian:
        raise ValueError("Tabel Huffman tidak valid")

    while len(antrian) > 1:
        frek1, _, kiri = heapq.heappop(antrian)
        frek2, _, kanan = heapq.heappop(antrian)

        heapq.heappush(
            antrian,
            (frek1 + frek2, next(nomor), (kiri, kanan))
        )

    pohon = antrian[0][2]

    if isinstance(pohon, int):
        return bytes([pohon]) * ukuran_asli

    hasil = bytearray()
    node = pohon

    for byte in isi:
        for posisi in range(7, -1, -1):
            bit = (byte >> posisi) & 1
            node = node[bit]

            if isinstance(node, int):
                hasil.append(node)
                node = pohon

                if len(hasil) == ukuran_asli:
                    return bytes(hasil)

    raise ValueError("Data Huffman tidak lengkap")


# =====================================
# ALGORITMA LZ77
# =====================================

def lz77_compress(data):
    hasil = bytearray()
    i = 0

    while i < len(data):
        jarak_terbaik = 0
        panjang_terbaik = 0

        awal = max(0, i - 255)

        for j in range(awal, i):
            panjang = 0

            while (
                i + panjang < len(data)
                and j + panjang < i
                and data[j + panjang] == data[i + panjang]
                and panjang < 255
            ):
                panjang += 1

            if panjang > panjang_terbaik:
                panjang_terbaik = panjang
                jarak_terbaik = i - j

        if panjang_terbaik >= 3:
            hasil.extend([1, jarak_terbaik, panjang_terbaik])
            i += panjang_terbaik
        else:
            hasil.extend([0, data[i]])
            i += 1

    return bytes(hasil)


def lz77_decompress(data):
    hasil = bytearray()
    i = 0

    while i < len(data):
        tipe = data[i]
        i += 1

        if tipe == 0:
            if i >= len(data):
                raise ValueError("Data LZ77 tidak lengkap")

            hasil.append(data[i])
            i += 1

        elif tipe == 1:
            if i + 1 >= len(data):
                raise ValueError("Data LZ77 tidak lengkap")

            jarak = data[i]
            panjang = data[i + 1]
            i += 2

            if jarak == 0 or jarak > len(hasil) or panjang == 0:
                raise ValueError("Data LZ77 tidak valid")

            for _ in range(panjang):
                hasil.append(hasil[-jarak])

        else:
            raise ValueError("Tipe data LZ77 tidak dikenal")

    return bytes(hasil)


# =====================================
# KOMPRESI DAN DEKOMPRESI FILE
# =====================================

def compress_file(data, algoritma):
    if algoritma == "RLE":
        payload = rle_compress(data)
        kode = b"R"

    elif algoritma == "Huffman":
        payload = huffman_compress(data)
        kode = b"H"

    elif algoritma == "LZ77":
        payload = lz77_compress(data)
        kode = b"L"

    else:
        raise ValueError("Algoritma tidak dikenal")

    header = b"COMP" + kode + struct.pack(">Q", len(data))

    return header + payload


def decompress_file(data):
    if len(data) < 13 or data[:4] != b"COMP":
        raise ValueError("Format file tidak valid")

    kode = data[4:5]
    ukuran_asli = struct.unpack(">Q", data[5:13])[0]
    payload = data[13:]

    if kode == b"R":
        hasil = rle_decompress(payload)

    elif kode == b"H":
        hasil = huffman_decompress(payload, ukuran_asli)

    elif kode == b"L":
        hasil = lz77_decompress(payload)

    else:
        raise ValueError("Algoritma tidak dikenal")

    if len(hasil) != ukuran_asli:
        raise ValueError("Ukuran hasil dekompresi tidak sesuai")

    return hasil


# =====================================
# KOMPRESI FOLDER
# =====================================

def compress_folder(files, algoritma):
    buffer = io.BytesIO()

    with zipfile.ZipFile(buffer, "w") as arsip:
        for file in files:
            nama = file.filename.replace("\\", "/")
            bagian = nama.split("/")

            if (
                not nama
                or nama.startswith("/")
                or ".." in bagian
                or (bagian and bagian[0].endswith(":"))
            ):
                continue

            data = file.read()
            hasil = compress_file(data, algoritma)

            arsip.writestr(
                nama,
                hasil,
                compress_type=zipfile.ZIP_STORED
            )

    return b"FOLD" + buffer.getvalue()


def decompress_folder(data):
    if not data.startswith(b"FOLD"):
        raise ValueError("Format kompresi folder tidak valid")

    buffer_masuk = io.BytesIO(data[4:])
    buffer_keluar = io.BytesIO()

    with zipfile.ZipFile(buffer_masuk, "r") as arsip_masuk:
        with zipfile.ZipFile(buffer_keluar, "w") as arsip_keluar:
            for item in arsip_masuk.infolist():
                nama = item.filename.replace("\\", "/")
                bagian = nama.split("/")

                if item.is_dir():
                    continue

                if (
                    not nama
                    or nama.startswith("/")
                    or ".." in bagian
                    or (bagian and bagian[0].endswith(":"))
                ):
                    raise ValueError("Nama file dalam folder tidak aman")

                isi_kompres = arsip_masuk.read(item.filename)
                isi_asli = decompress_file(isi_kompres)

                arsip_keluar.writestr(nama, isi_asli)

    return buffer_keluar.getvalue()


# =====================================
# HALAMAN UTAMA
# =====================================

@app.route("/")
def home():
    return render_template("index.html")


# =====================================
# KOMPRESI FILE
# =====================================

@app.route("/compress", methods=["POST"])
def compress():
    file = request.files.get("file")
    algoritma = normalisasi_algoritma(
        request.form.get("algoritma")
    )

    if not file or not file.filename:
        return render_template(
            "index.html",
            error="Silakan pilih file terlebih dahulu"
        )

    if algoritma not in EKSTENSI:
        return render_template(
            "index.html",
            error="Algoritma tidak valid"
        )

    nama_file = secure_filename(file.filename)

    if not nama_file:
        return render_template(
            "index.html",
            error="Nama file tidak valid"
        )

    try:
        data = file.read()

        mulai = time.perf_counter()
        hasil = compress_file(data, algoritma)
        waktu = time.perf_counter() - mulai

        nama_hasil = (
            os.path.splitext(nama_file)[0]
            + EKSTENSI[algoritma]
        )

        lokasi = os.path.join(RESULT_FOLDER, nama_hasil)

        with open(lokasi, "wb") as f:
            f.write(hasil)

        ukuran_awal = len(data)
        ukuran_akhir = len(hasil)

        rasio = (
            ((ukuran_awal - ukuran_akhir) / ukuran_awal) * 100
            if ukuran_awal > 0 else 0
        )

        return render_template(
            "index.html",
            nama_file=nama_file,
            nama_hasil=nama_hasil,
            ukuran_awal=ukuran_awal,
            ukuran_akhir=ukuran_akhir,
            waktu=round(waktu, 6),
            rasio=round(rasio, 2),
            algoritma=algoritma,
            mode="kompresi"
        )

    except Exception as e:
        return render_template(
            "index.html",
            error="Gagal kompresi: " + str(e)
        )


# =====================================
# DEKOMPRESI FILE
# =====================================

@app.route("/decompress", methods=["POST"])
def decompress():
    file = request.files.get("file")

    if not file or not file.filename:
        return render_template(
            "index.html",
            error="Pilih file kompresi terlebih dahulu"
        )

    nama_file = secure_filename(file.filename)

    try:
        data = file.read()

        mulai = time.perf_counter()
        hasil = decompress_file(data)
        waktu = time.perf_counter() - mulai

        nama_hasil = nama_file + ".hasil"
        lokasi = os.path.join(RESULT_FOLDER, nama_hasil)

        with open(lokasi, "wb") as f:
            f.write(hasil)

        return render_template(
            "index.html",
            nama_file=nama_file,
            nama_hasil=nama_hasil,
            ukuran_akhir=len(hasil),
            waktu=round(waktu, 6),
            mode="dekompresi"
        )

    except Exception as e:
        return render_template(
            "index.html",
            error="Gagal dekompresi: " + str(e)
        )


# =====================================
# KOMPRESI FOLDER
# =====================================

@app.route("/compress-folder", methods=["POST"])
def compress_folder_route():
    files = request.files.getlist("files")
    files = [file for file in files if file.filename]

    algoritma = normalisasi_algoritma(
        request.form.get("algoritma")
    )

    if not files:
        return render_template(
            "index.html",
            error="Silakan pilih folder terlebih dahulu"
        )

    if algoritma not in EKSTENSI:
        return render_template(
            "index.html",
            error="Algoritma tidak valid"
        )

    try:
        ukuran_awal = 0

        for file in files:
            data = file.read()
            ukuran_awal += len(data)
            file.seek(0)

        mulai = time.perf_counter()
        hasil = compress_folder(files, algoritma)
        waktu = time.perf_counter() - mulai

        nama_folder = secure_filename(
            request.form.get("folder_name", "folder")
        ) or "folder"

        nama_hasil = nama_folder + EKSTENSI[algoritma]
        lokasi = os.path.join(RESULT_FOLDER, nama_hasil)

        with open(lokasi, "wb") as f:
            f.write(hasil)

        ukuran_akhir = len(hasil)

        rasio = (
            ((ukuran_awal - ukuran_akhir) / ukuran_awal) * 100
            if ukuran_awal > 0 else 0
        )

        return render_template(
            "index.html",
            nama_file=nama_folder,
            nama_hasil=nama_hasil,
            ukuran_awal=ukuran_awal,
            ukuran_akhir=ukuran_akhir,
            waktu=round(waktu, 6),
            rasio=round(rasio, 2),
            algoritma=algoritma,
            mode="kompresi_folder",
            jumlah_file=len(files)
        )

    except Exception as e:
        return render_template(
            "index.html",
            error="Gagal kompres folder: " + str(e)
        )


# =====================================
# DEKOMPRESI FOLDER
# =====================================

@app.route("/decompress-folder", methods=["POST"])
def decompress_folder_route():
    file = request.files.get("file")

    if not file or not file.filename:
        return render_template(
            "index.html",
            error="Pilih file kompresi folder terlebih dahulu"
        )

    try:
        data = file.read()

        mulai = time.perf_counter()
        hasil = decompress_folder(data)
        waktu = time.perf_counter() - mulai

        nama_asli = secure_filename(file.filename)
        nama_hasil = nama_asli + ".hasil.zip"

        lokasi = os.path.join(RESULT_FOLDER, nama_hasil)

        with open(lokasi, "wb") as f:
            f.write(hasil)

        return render_template(
            "index.html",
            nama_file=nama_asli,
            nama_hasil=nama_hasil,
            ukuran_akhir=len(hasil),
            waktu=round(waktu, 6),
            mode="dekompresi_folder"
        )

    except Exception as e:
        return render_template(
            "index.html",
            error="Gagal dekompres folder: " + str(e)
        )


# =====================================
# DOWNLOAD HASIL
# =====================================

@app.route("/download/<nama_file>")
def download(nama_file):
    return send_from_directory(
        RESULT_FOLDER,
        nama_file,
        as_attachment=True
    )


if __name__ == "__main__":
    app.run(debug=True)
