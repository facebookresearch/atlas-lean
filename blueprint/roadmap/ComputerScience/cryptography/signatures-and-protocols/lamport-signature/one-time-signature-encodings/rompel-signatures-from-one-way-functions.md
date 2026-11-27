# Rompel: one-way functions are necessary and sufficient for secure signatures

One-way functions exist if and only if there is a stateless signature scheme on arbitrary-length messages that is existentially unforgeable under adaptive chosen-message attack.

## Proof sketch

Necessity is the coins-to-public-key argument. For sufficiency, one-way functions give pseudorandom functions, Lamport one-time signatures, and (by Rompel's theorem) target collision-resistant hashing; TCR hash-and-sign makes the one-time scheme sign long messages, and the stateless PRF-seeded authentication tree turns it into a many-time scheme.

## Depends on

- [One-way function families](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)

## Proof depends on

- [Secure signatures imply one-way functions, and one-way functions give one-time signatures](signatures-and-one-way-functions.md)
- [Rompel: one-way functions yield universal one-way hash functions](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/inaccessible-entropy-and-universal-one-way-hashing/rompel-one-way-functions-yield-uowhfs.md)
- [Signing a fresh target collision-resistant hash extends signatures to long messages](tcr-hash-and-sign.md)
- [Stateless tree signatures from an indexed scheme and a PRF](stateless-tree-signatures.md)
- [One-way functions imply adaptively secure pseudorandom functions](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/hard-core-predicates-and-stretch/one-way-functions-imply-pseudorandom-functions.md)

## Sources

- J. Rompel, "One-Way Functions are Necessary and Sufficient for Secure Signatures", Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC), 1990.
- M. Naor and M. Yung, "Universal One-Way Hash Functions and their Cryptographic Applications", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
- O. Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
