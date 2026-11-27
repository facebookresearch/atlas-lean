# Generic composition counterexamples for authenticated encryption

(a) *Encrypt-and-MAC*, which outputs $E(k_e, m)$ together with a deterministic tag $S(k_m, m)$, is not CPA secure for any deterministic MAC that is unforgeable, provided the message space contains two distinct messages of equal length: equal messages produce equal tags, while unforgeability makes the tags of two distinct messages differ except with negligible probability. (b) If a CPA-secure cipher with plaintext integrity exists, then there is a CPA-secure cipher with plaintext integrity that is neither CCA secure nor has ciphertext integrity: modify such a cipher so that decryption ignores a trailing ciphertext bit. (c) Assuming CPA-secure ciphers and strongly unforgeable MACs exist, there are a CPA-secure cipher and a strongly unforgeable MAC whose *MAC-then-encrypt* composition is not CCA secure (for example with a cipher whose decryption accepts several encodings of the same padded plaintext). Encrypt-then-MAC of a CPA-secure cipher and a strongly unforgeable MAC under independent keys is authenticated encryption, so it is the generic composition that always yields authenticated encryption.

## Proof sketch

(a) Query the pair $(m, m)$ and then $(m, m')$ for distinct $m, m'$ of equal length in the left-or-right game, and compare the two tags. (b) Flipping the ignored bit produces a fresh ciphertext of a queried message: it breaks CCA security and ciphertext integrity but not plaintext integrity. (c) Re-encode the challenge's padding and query decryption.

## Depends on

- [Authenticated encryption](authenticated-encryption.md)
- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [Encrypt-then-authenticate](../encrypt-then-mac/scheme.md)
- [Polynomial-query unforgeability of MACs](../../security-games/asymptotic-security/poly-query-macsecure.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Encrypt-then-MAC is CCA-secure](../encrypt-then-mac/cca-advantage-le.md)

## Sources

- M. Bellare and C. Namprempre, "Authenticated Encryption: Relations among Notions and Analysis of the Generic Composition Paradigm", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
