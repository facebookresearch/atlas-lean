# A stream cipher with a linear checksum has no ciphertext integrity

Let a cipher encrypt $m$ as a keystream XOR of $m \,\|\, \mathrm{chk}(m)$, where $\mathrm{chk}$ is $\mathbb{F}_2$-linear (for instance a CRC). Then for every $\Delta$, XORing $\Delta \,\|\, \mathrm{chk}(\Delta)$ into a ciphertext of $m$ produces a valid ciphertext of $m \oplus \Delta$, so the scheme has no ciphertext integrity and no plaintext integrity, whatever the keystream.

## Proof sketch

Linearity gives $\mathrm{chk}(m \oplus \Delta) = \mathrm{chk}(m) \oplus \mathrm{chk}(\Delta)$, so the modified body is the keystream XOR of a well-formed encoding.

## Depends on

- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [Ciphertext integrity](../../security-games/generic-security-games/ctxt-game.md)

## Sources

- Nikita Borisov, Ian Goldberg and David Wagner, "Intercepting Mobile Communications: The Insecurity of 802.11", Proceedings of the Seventh Annual International Conference on Mobile Computing and Networking (MobiCom 2001), ACM, 2001, Section 4.1.
