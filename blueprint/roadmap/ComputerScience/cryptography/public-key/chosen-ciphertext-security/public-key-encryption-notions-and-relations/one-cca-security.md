# 1CCA security of public-key encryption

A public-key scheme is *1CCA secure* if every efficient adversary has negligible advantage in the experiment where it receives the public key, may query a decryption oracle, submits one equal-length challenge pair $(m_0, m_1)$, receives $c^* = E(pk, m_b)$, may query decryption of every ciphertext other than $c^*$, and outputs a guess for $b$. *Non-adaptive* CCA allows decryption queries only before the challenge. *Batch* or *multi-challenge* CCA allows polynomially many challenge pairs under a common bit, with decryption of all challenge ciphertexts forbidden.

## Depends on

- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
