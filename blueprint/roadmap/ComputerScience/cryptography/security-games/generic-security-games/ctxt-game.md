# Ciphertext integrity

**Ciphertext integrity** (`INT-CTXT`; Bellare and Namprempre; the ciphertext form of Katz
and Lindell's unforgeable encryption, Section 4.5): `k ← Gen`, the forger runs with oracle
`Enc_k` and outputs `c`; it wins when `Dec_k(c) ≠ ⊥` and `c` was never an oracle answer.
