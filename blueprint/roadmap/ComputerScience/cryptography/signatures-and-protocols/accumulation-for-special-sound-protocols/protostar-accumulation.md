# ProtoStar: generic accumulation for special-sound protocols

Let $\Pi$ be a $(2k-1)$-move special-sound protocol, with negligible knowledge error, whose verifier checks $\ell$ algebraic equations of degree $d$ over a field with $|\mathbb{F}|\ge2^{\lambda}$. Committing to the prover messages with a binding additively homomorphic commitment and applying the Fiat–Shamir transform yields a NARK, and this NARK has an accumulation scheme in the random oracle model, with perfect completeness and knowledge error $(Q+1)(d+1)/|\mathbb{F}|+\mathrm{negl}(\lambda)$ against $Q$-query adversaries ($(Q+1)(d+4)/|\mathbb{F}|+\mathrm{negl}(\lambda)$ for the compressed variant below). After all verification equations are compressed into one by a random linear combination, the accumulation verifier performs $k+2$ group scalar multiplications and $k+d+O(1)$ field and hash operations (without compression, $k+d-1$ group scalar multiplications). If $\Pi$ is a protocol for an NP-complete relation, applying the compiler from NARKs with accumulation to IVC, under the Fiat–Shamir heuristic for a concrete hash function, gives IVC schemes whose recursive circuit depends only on $k$ and $d$, not on the proof size or verifier time of $\Pi$; this covers high-degree Plonkish constraint systems with lookups.

## Proof sketch

The accumulator is a relaxed transcript with committed messages, a slack $\mu$ and a committed error. Folding uses the error polynomial: the prover commits to its $d-1$ intermediate coefficients and a random $\alpha$ combines accumulator and new proof linearly, so the verifier only combines commitments homomorphically. Soundness: from $d+1$ accepting folds with distinct $\alpha$ one interpolates the error polynomial, and binding together with knowledge soundness of the Fiat–Shamir NARK yields witnesses for both inputs.

## Depends on

- [Split accumulation and NARKs with accumulation](../incrementally-verifiable-computation-and-pcd/split-accumulation.md)
- [Special-sound protocols with algebraic degree-d verifiers](special-sound-algebraic-verifier.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Proof-carrying data for a compliance predicate](../incrementally-verifiable-computation-and-pcd/pcd-scheme.md)

## Proof depends on

- [Error polynomial when folding relaxed degree-d verifier checks](protostar-error-polynomial.md)
- [Compressing the relaxed verifier output with powers of a challenge](protostar-compressed-verification.md)
- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Proof-carrying data from NARKs with split accumulation](../incrementally-verifiable-computation-and-pcd/pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620, abstract, Section 1, Theorem 2, Theorem 3 and Corollary 2.
