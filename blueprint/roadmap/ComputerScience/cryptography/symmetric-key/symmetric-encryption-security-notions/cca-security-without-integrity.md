# CCA security does not imply ciphertext or plaintext integrity

If pseudorandom functions exist, there is a CCA-secure symmetric cipher with neither ciphertext integrity nor plaintext integrity. Instantiate the half-block cipher, with $n$ the security parameter (so $2^{-n}$ is negligible), with the four-round Feistel strong PRP on $2n$-bit blocks built from a PRF on $n$-bit blocks; the forger that submits $1^{2n}$ without any encryption query wins the plaintext-integrity game with probability $1$, because every $2n$-bit word decrypts to some message.

## Proof sketch

CCA security is the half-block theorem with the Luby–Rackoff four-round strong PRP. Decryption never rejects a word of the right length, so any word is a forgery of some message that, with no encryption queries, is fresh.

## Depends on

- [Plaintext integrity (fresh-message unforgeability)](plaintext-integrity.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Half-block encryption with a strong PRP is CCA secure](half-block-encryption-cca-security.md)
- [Luby–Rackoff theorem](../pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.
