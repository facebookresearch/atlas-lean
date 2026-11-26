# Transparent PCD from accumulation of discrete-log inner-product arguments

In the random oracle model, if the inner-product-argument polynomial commitment $\mathsf{PC}_{\mathrm{DL}}$ is a polynomial commitment scheme (as it is under the hardness of discrete logarithms in a prime-order group), then it has a zero-knowledge accumulation scheme in which, for $n$ evaluation claims and $m$ old accumulators about polynomials of degree at most $d$, the accumulation verifier performs $O((n+m)\log d)$ scalar multiplications, the decider performs $O(d)$, the accumulation prover $O(n+m+d)$, and the accumulator is one group element plus an evaluation proof of $O(\log d)$ group elements. Combined with a SNARK whose verifier is succinct given oracle access to $\mathsf{PC}_{\mathrm{DL}}$ checks, this gives a SNARK with an accumulation scheme in the random oracle model. Heuristically instantiating the random oracle with a hash function, and applying the compiler from SNARKs with accumulation to PCD, which holds in the standard model, yields PCD for polynomial-time compliance predicates in the uniform reference string model, without secret parameters; the PCD conclusion is heuristic because of that instantiation.

## Proof sketch

Accumulators and inputs are both evaluation claims, so the scheme accumulates claims only. Each claim's succinct check outputs a pair $(h_i,U_i)$ whose remaining check "$U_i$ commits to $h_i$" is combined by a random linear combination and opened once at a random-oracle point; the accumulation verifier repeats the succinct checks and the combination, and the decider runs the full check of one evaluation proof. The general compiler from SNARKs with accumulation to PCD then applies to the instantiated scheme.

## Depends on

- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)

## Proof depends on

- [Deferring the linear-time check of inner-product arguments](halo-deferred-ipa-check.md)
- [Proof-carrying data from NARKs with split accumulation](pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499, Section 1.1 (Theorems 1 to 3 and the heuristic PCD constructions), Theorem 7.1, Section 7.1 and Appendix A.
