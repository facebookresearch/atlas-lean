# Plaintext integrity (fresh-message unforgeability)

A symmetric cipher has *plaintext integrity* if every efficient adversary with an encryption oracle wins the following game with negligible probability: it outputs a ciphertext $c$ whose decryption is a message $m \ne \bot$ that was never submitted to the encryption oracle. This is weaker than ciphertext integrity, which also counts new ciphertexts of previously encrypted messages.

## Depends on

- [Ciphertext integrity](../../security-games/generic-security-games/ctxt-game.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
