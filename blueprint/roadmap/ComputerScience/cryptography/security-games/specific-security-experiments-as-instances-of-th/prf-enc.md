# Prf Enc

PRF encryption `Enc_k(m) = (r, F k r + m)` with a uniform key and uniform fresh randomness
`r` (Katz and Lindell, Construction 3.30): the `EncryptThenMac.coinScheme` that encrypts with
`PRF.encrypt (F k) m r` and decrypts with `PRF.decrypt (F k)`.
