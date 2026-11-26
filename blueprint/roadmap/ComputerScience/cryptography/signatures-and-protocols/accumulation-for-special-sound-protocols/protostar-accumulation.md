# ProtoStar: generic accumulation for special-sound protocols

Let $\Pi$ be a $(2k-1)$-move special-sound protocol for $\mathcal{R}$ with an algebraic verifier of degree $d$ and output length $\ell$. Compiling $\Pi$ with a binding additively homomorphic commitment to the prover messages and the Fiat–Shamir transform yields a NARK, and this NARK admits an accumulation scheme in the random oracle model whose accumulation verifier performs a number of group scalar multiplications linear in $k$ (one per committed message) plus $O(1)$ for the committed error terms, $O(d)$ field operations and one hash, independently of $\ell$ when compressed verification is used. By the compiler from NARKs with accumulation, this gives IVC/PCD for any relation with such a protocol, in particular for high-degree Plonkish constraint systems.

## Proof sketch

The accumulator is a relaxed transcript with committed messages, slack $\mu$ and a committed error. Folding uses the error polynomial: the prover commits to the $d-1$ intermediate coefficients and a random $\alpha$ combines everything linearly, so the verifier only combines commitments homomorphically. Soundness: from $d+1$ accepting folds with distinct $\alpha$ one interpolates the error polynomial, and special soundness of $\Pi$ together with binding yields witnesses for both inputs.

## Depends on

- [Error polynomial when folding relaxed degree-d verifier checks](protostar-error-polynomial.md)
- [Compressing the relaxed verifier output with powers of a challenge](protostar-compressed-verification.md)
- [Split accumulation and NARKs with accumulation](../incrementally-verifiable-computation-and-pcd/split-accumulation.md)
- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)

## Proof depends on

- [Error polynomial when folding relaxed degree-d verifier checks](protostar-error-polynomial.md)
- [Proof-carrying data from NARKs with split accumulation](../incrementally-verifiable-computation-and-pcd/pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620.
