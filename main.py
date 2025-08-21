# main.py
import streamlit as st
from collections import OrderedDict
from datetime import datetime, timezone
import hashlib, json, math
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import (
    encode_dss_signature, decode_dss_signature
)
from cryptography.exceptions import InvalidSignature

# ------------------ Helpers ------------------
def canonical_json(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec='seconds')

def tx_hash(tx: dict) -> str:
    payload = {k: v for k, v in tx.items() if k != 'signature'}
    return sha256_hex(canonical_json(payload))

def merkle_root(tx_hashes):
    if not tx_hashes:
        return sha256_hex(b'')
    layer = list(tx_hashes)
    while len(layer) > 1:
        nxt = []
        for i in range(0, len(layer), 2):
            a = layer[i]
            b = layer[i+1] if i+1 < len(layer) else layer[i]
            nxt.append(sha256_hex((a + b).encode()))
        layer = nxt
    return layer[0]

def merkle_proof(tx_hashes, idx):
    if idx < 0 or idx >= len(tx_hashes):
        return []
    proof = []
    layer = list(tx_hashes)
    pos = idx
    while len(layer) > 1:
        nxt = []
        for i in range(0, len(layer), 2):
            a = layer[i]
            b = layer[i+1] if i+1 < len(layer) else layer[i]
            nxt.append(sha256_hex((a + b).encode()))
        is_right = (pos % 2 == 1)
        sib_idx = pos-1 if is_right else pos+1
        if sib_idx >= len(layer):
            sib_idx = pos
        sibling = layer[sib_idx]
        direction = 'L' if is_right else 'R'
        proof.append((sibling, direction))
        pos = pos // 2
        layer = nxt
    return proof

def verify_merkle_inclusion(leaf_hash, proof, root):
    cur = leaf_hash
    for sib, direction in proof:
        if direction == 'L':
            cur = sha256_hex((sib + cur).encode())
        else:
            cur = sha256_hex((cur + sib).encode())
    return cur == root

# ------------------ Keys & Signatures ------------------
def gen_ec_key():
    return ec.generate_private_key(ec.SECP256R1())

def pub_pem(pub):
    return pub.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    ).decode()

def sign_ec(priv, message_bytes: bytes) -> str:
    sig = priv.sign(message_bytes, ec.ECDSA(hashes.SHA256()))
    r, s = decode_dss_signature(sig)
    return f"{r:064x}{s:064x}"

def verify_ec(pub, message_bytes: bytes, sig_hex: str) -> bool:
    try:
        r = int(sig_hex[:64], 16)
        s = int(sig_hex[64:], 16)
        der = encode_dss_signature(r, s)
        pub.verify(der, message_bytes, ec.ECDSA(hashes.SHA256()))
        return True
    except InvalidSignature:
        return False
    except Exception:
        return False

# ------------------ Classes ------------------
class Doctor:
    def __init__(self, doc_id: str):
        self.id = doc_id
        self.priv = gen_ec_key()
        self.pub = self.priv.public_key()
    def public_pem(self): return pub_pem(self.pub)

class Validator:
    def __init__(self, vid: str):
        self.id = vid
        self.priv = gen_ec_key()
        self.pub = self.priv.public_key()
    def sign_blockhash(self, blk_hash: str) -> str:
        return sign_ec(self.priv, blk_hash.encode())
    def verify_blockhash(self, blk_hash: str, sig_hex: str) -> bool:
        return verify_ec(self.pub, blk_hash.encode(), sig_hex)

class Block:
    def __init__(self, index, prev_hash, proposer_id, txs):
        self.index = index
        self.timestamp = utc_now_iso()
        self.prev_hash = prev_hash
        self.txs = list(txs)
        self.tx_hashes = [tx_hash(t) for t in self.txs]
        self.merkle_root = merkle_root(self.tx_hashes)
        self.proposer_id = proposer_id
        self.header = {
            "index": self.index,
            "timestamp": self.timestamp,
            "prev_hash": self.prev_hash,
            "merkle_root": self.merkle_root,
            "proposer_id": self.proposer_id
        }
        self.hash = sha256_hex(canonical_json(self.header))
        self.approvals = {}
    def as_dict(self):
        return {
            "index": self.index,
            "timestamp": self.timestamp,
            "prev_hash": self.prev_hash,
            "merkle_root": self.merkle_root,
            "proposer_id": self.proposer_id,
            "hash": self.hash,
            "approvals": self.approvals,
            "transactions": self.txs
        }

class Blockchain:
    def __init__(self, validators, quorum_ratio=2/3):
        self.validators = {v.id: v for v in validators}
        self.quorum = math.ceil(quorum_ratio * len(validators))
        self.chain = [self._genesis()]
        self.pending = []
        self._round_robin = 0
    def _genesis(self):
        b = Block(0, "0"*64, "GENESIS", [])
        for vid, v in self.validators.items():
            b.approvals[vid] = v.sign_blockhash(b.hash)
        return b
    def add_prescription(self, tx):
        self.pending.append(tx)
    def _next_proposer(self):
        vids = list(self.validators.keys())
        proposer_id = vids[self._round_robin % len(vids)]
        self._round_robin += 1
        return self.validators[proposer_id]
    def mine_with_poa(self):
        if not self.pending: return None
        last = self.chain[-1]
        proposer = self._next_proposer()
        block = Block(last.index+1, last.hash, proposer.id, self.pending)
        self.pending = []
        block.approvals[proposer.id] = proposer.sign_blockhash(block.hash)
        for vid, val in self.validators.items():
            if vid == proposer.id: continue
            block.approvals[vid] = val.sign_blockhash(block.hash)
            if len(block.approvals) >= self.quorum: break
        if self.is_block_valid(block):
            self.chain.append(block)
            return block
        return None
    def is_block_valid(self, blk):
        if blk.prev_hash != self.chain[-1].hash: return False
        if blk.merkle_root != merkle_root([tx_hash(t) for t in blk.txs]): return False
        if len(blk.approvals) < self.quorum: return False
        for vid, sig in blk.approvals.items():
            v = self.validators.get(vid)
            if not v or not v.verify_blockhash(blk.hash, sig): return False
        return True
    def find_tx_by_sig(self, signature_hex):
        for b in self.chain:
            for i, t in enumerate(b.txs):
                if t.get("signature") == signature_hex:
                    return b, i, t
        return None, None, None

# ------------------ Global State ------------------
if "doctors" not in st.session_state:
    st.session_state.doctors = {}
if "validators" not in st.session_state:
    st.session_state.validators = [Validator("AUTH1"), Validator("AUTH2"), Validator("AUTH3")]
if "chain" not in st.session_state:
    st.session_state.chain = Blockchain(st.session_state.validators)

doctors = st.session_state.doctors
validators = st.session_state.validators
chain = st.session_state.chain

# ------------------ Streamlit UI ------------------
# ================== Project Info Section ==================
st.title("🏥 Dosochain - Blockchain-based Prescription System")



menu = st.sidebar.radio("Menu", [
    "Home",
    "Register Doctor",
    "Issue Prescription",
    "Mine Block",
    "Verify Prescription",
    "View Blockchain",
    "List Doctors & Validators"
])
if menu == "Home":
    st.markdown("""
    ### 📌 Description
    Dosochain is a simple blockchain prototype for **secure prescription issuing and verification**.  
    It ensures that prescriptions issued by doctors cannot be tampered with and can be verified by pharmacies or patients.
    Created by **Ahamed H** and **Aashif M**
     
    ---

    ### 🔑 Working
    1. Doctors register and generate a public/private key pair.  
    2. A doctor issues a prescription which is digitally signed.  
    3. Prescriptions are added as transactions to a blockchain.  
    4. Validators (Proof of Authority) mine blocks to confirm pending prescriptions.  
    5. A Merkle Tree ensures prescriptions can be verified quickly.  
    6. Verification checks:
       - ✅ Doctor’s digital signature  
       - ✅ Inclusion in blockchain  

    ---

    ### 💡 Use Cases
    - 🏥 **Hospitals** → Issue tamper-proof prescriptions  
    - 💊 **Pharmacies** → Verify before dispensing medicines  
    - 👨‍⚕️ **Patients** → Ensure authenticity of prescriptions  
    - 🛡️ **Medical Regulators** → Prevent fraud and fake prescriptions  

    ---

    ### ⚙️ Algorithms Used
    - 🔐 **SHA-256 Hashing** → Prescription integrity & immutability  
    - ✍️ **ECDSA Digital Signatures** → Doctor authorization  
    - ⛓️ **Proof of Authority Consensus** → Block validation  
    - 🌳 **Merkle Tree Algorithm** → Fast verification  
    - ⏱️ **Time-stamping** → Track when prescriptions were issued  
    """)

elif menu == "Register Doctor":
    st.subheader("Register Doctor")
    doc_id = st.text_input("Doctor ID")
    if st.button("Register"):
        if doc_id in doctors:
            st.warning("Doctor already exists")
        else:
            d = Doctor(doc_id)
            doctors[doc_id] = d
            st.success(f"Doctor {doc_id} registered")
            st.code(d.public_pem())

elif menu == "Issue Prescription":
    st.subheader("Issue Prescription")
    if not doctors:
        st.warning("Register a doctor first")
    else:
        doc_id = st.selectbox("Doctor", list(doctors.keys()))
        pat = st.text_input("Patient ID")
        med = st.text_input("Medicine")
        dose = st.text_input("Dosage")
        if st.button("Create Prescription"):
            presc = OrderedDict([
                ("patient_id", pat),
                ("doctor_id", doc_id),
                ("medicine", med),
                ("dosage", dose),
                ("issued_time", utc_now_iso())
            ])
            sig = sign_ec(doctors[doc_id].priv, canonical_json(presc))
            presc["signature"] = sig
            chain.add_prescription(presc)
            st.success("Prescription created (pending) copy the signature shown now for verification")
            st.code(sig)

elif menu == "Mine Block":
    st.subheader("Mine Block (PoA)")
    if st.button("Mine"):
        block = chain.mine_with_poa()
        if block:
            st.success("✅ Prescription Block Mined Successfully!")
            st.write(f"**Block Index:** {block.index}")
            st.write(f"**Timestamp:** {block.timestamp}")
            st.write(f"**Block Hash:** {block.hash}")

        else:
            st.warning("No pending prescriptions")

elif menu == "Verify Prescription":
    st.subheader("Verify Prescription")
    sig = st.text_input("Prescription Signature")
    if st.button("Verify"):
        blk, idx, tx = chain.find_tx_by_sig(sig)
        if not tx:
            st.error("Not found on chain")
        else:
            payload = {k: v for k, v in tx.items() if k != "signature"}
            doc = doctors.get(payload["doctor_id"])
            ok_sig = verify_ec(doc.pub, canonical_json(payload), tx["signature"]) if doc else False
            tx_hashes = [tx_hash(t) for t in blk.txs]
            leaf = tx_hash(tx)
            proof = merkle_proof(tx_hashes, idx)
            ok_merkle = verify_merkle_inclusion(leaf, proof, blk.merkle_root)
            st.json({
                "Block": blk.index,
                "Signature valid": ok_sig,
                "Merkle inclusion valid": ok_merkle
            })
            if ok_sig and ok_merkle:
                st.success("✅ Prescription authentic & on-chain")
            else:
                st.error("❌ Verification failed")

elif menu == "View Blockchain":
    st.subheader("Blockchain Explorer")
    for b in chain.chain:
        with st.expander(f"Block {b.index}"):
            st.json(b.as_dict())

elif menu == "List Doctors & Validators":
    st.subheader("Doctors")
    st.write(list(doctors.keys()))
    st.subheader("Validators")
    st.write([v.id for v in validators])
