# Authenticated encryption

A symmetric cipher provides *authenticated encryption* if it is CPA secure and has ciphertext integrity: no efficient adversary with an encryption oracle outputs, with non-negligible probability, a ciphertext not returned by the oracle that decrypts to a message (rather than to a rejection). *One-time* authenticated encryption allows a single encryption query in both games.

## Depends on

- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)
- [Ciphertext integrity](../../security-games/generic-security-games/ctxt-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
