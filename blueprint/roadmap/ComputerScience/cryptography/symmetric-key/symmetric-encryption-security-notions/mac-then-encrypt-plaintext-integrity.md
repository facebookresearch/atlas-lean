# MAC-then-encrypt has plaintext integrity

Let $M$ be a secure (existentially unforgeable) MAC on $n$-bit messages and $E$ any correct symmetric cipher on the framed pairs. The MAC-then-encrypt cipher, which encrypts $(m, S(k_m, m))$ under $k_e$ and on decryption rejects unless the plaintext is a well-formed pair whose tag verifies, has plaintext integrity.

## Proof sketch

A ciphertext decrypting to a fresh message $m$ yields a pair $(m, t)$ with $V(k_m, m, t)$ accepting. The MAC forger simulates the encryption oracle by tagging with its own oracle and encrypting with a key it chooses, so a plaintext forgery is a MAC forgery on a message never tagged.

## Depends on

- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [Message authentication code](../../security-games/generic-security-games/macscheme.md)
- [MAC forgery experiment](../../security-games/generic-security-games/mac-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
