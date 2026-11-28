# Bitwise encryption of multi-bit messages from single-bit CPA security

Let a public-key scheme encrypt single bits and be CPA secure. Encrypting an $\ell$-bit message bit by bit with independent randomness gives a CPA-secure scheme for $\ell$-bit messages, with advantage at most $\ell$ times the single-bit advantage of a reduction.

## Proof sketch

Hybrid over positions: hybrid $j$ encrypts the first $j$ bits of $m_1$ and the remaining bits of $m_0$; adjacent hybrids differ in one bit encryption, which the reduction embeds from its challenge, encrypting the other positions itself with the public key.

## Depends on

- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Proof depends on

- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic Encryption", Journal of Computer and System Sciences 28(2), 1984.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
