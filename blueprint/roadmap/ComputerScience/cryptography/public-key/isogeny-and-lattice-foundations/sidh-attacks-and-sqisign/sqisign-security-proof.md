# A complete security proof of SQIsign in the random oracle model

SQIsign, as submitted to the second round of NIST's additional call for post-quantum signatures, is existentially unforgeable under chosen-message attacks in the random oracle model, assuming the hardness of the One Endomorphism problem with hints, or alternatively the hardness of the Full Endomorphism Ring problem with hints together with a hint indistinguishability assumption. All assumptions are non-interactive, in contrast with earlier interactive or heuristic assumptions on the distribution of responses.

## Proof sketch

Cast SQIsign as a Sigma protocol with hints, where the hint is a distribution of auxiliary isogenies or ideals enabling simulation of responses. The generic Fiat–Shamir-with-hints theorem reduces unforgeability to special soundness against an adversary given hints, and special soundness yields a non-scalar endomorphism (One Endomorphism) from two responses. Intermediate results analyze the distribution of the response isogenies.

## Depends on

- [Fiat–Shamir with hints](fiat-shamir-with-hints.md)
- [SQIsign: compact signatures from the SQIsign identification protocol](sqisign-signature.md)
- [The supersingular isogeny path and endomorphism ring problems](../supersingular-isogenies-and-quaternion-orders/isogeny-path-and-endring-problems.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Marius A. Aardal, Andrea Basso, Luca De Feo, Sikhar Patranabis, Benjamin Wesolowski, "A Complete Security Proof of SQIsign", CRYPTO (2025), IACR ePrint 2025/379.
