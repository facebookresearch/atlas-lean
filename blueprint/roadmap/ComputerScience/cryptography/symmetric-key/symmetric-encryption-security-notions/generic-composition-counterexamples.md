# Generic composition counterexamples for authenticated encryption

(a) *Encrypt-and-MAC*, which outputs $E(k_e, m)$ together with a deterministic tag $S(k_m, m)$, is not CPA secure for any deterministic MAC: equal messages produce equal tags. (b) There are CPA-secure ciphers with plaintext integrity that are neither CCA secure nor have ciphertext integrity: modify a cipher so that decryption ignores a trailing ciphertext bit. (c) *MAC-then-encrypt* with a CPA-secure cipher need not be CCA secure (for example with a cipher whose decryption accepts several encodings of the same padded plaintext). Encrypt-then-MAC with a strongly unforgeable MAC is the generic composition that always yields authenticated encryption.

## Proof sketch

(a) Query the same message twice in the left-or-right game against a different message. (b) Flipping the ignored bit produces a fresh ciphertext of a queried message: it breaks CCA security and ciphertext integrity but not plaintext integrity. (c) Re-encode the challenge's padding and query decryption.

## Depends on

- [Authenticated encryption](authenticated-encryption.md)
- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [Encrypt-then-authenticate](../encrypt-then-mac/scheme.md)

## Proof depends on

- [Encrypt-then-MAC is CCA-secure](../encrypt-then-mac/cca-advantage-le.md)

## Sources

- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
