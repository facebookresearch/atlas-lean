# Transparent PCD from accumulation of discrete-log inner-product arguments

In the random oracle model, assuming hardness of the discrete logarithm problem in a prime-order group, the inner-product-argument polynomial commitment scheme has an accumulation scheme whose accumulation verifier performs $O(\log d)$ group operations for degree-$d$ polynomials. Consequently there exists a SNARK with accumulation and hence (heuristically instantiating the random oracle inside recursion) PCD for every polynomial-time compliance predicate with a transparent (public-coin) setup.

## Proof sketch

Accumulation follows from the deferred check: each accumulator is a polynomial-evaluation claim about the generator commitment $G'$ to $h$, combined by random linear combination and opened once by the decider. Soundness reduces to the evaluation binding of the commitment, which reduces to discrete logarithms. The general compiler from SNARKs with accumulation to PCD then applies.

## Depends on

- [Deferring the linear-time check of inner-product arguments](halo-deferred-ipa-check.md)
- [Proof-carrying data from NARKs with split accumulation](pcd-from-accumulation.md)
- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Deferring the linear-time check of inner-product arguments](halo-deferred-ipa-check.md)
- [Proof-carrying data from NARKs with split accumulation](pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499.
- Sean Bowe, Jack Grigg, Daira Hopwood, "Recursive Proof Composition without a Trusted Setup", IACR ePrint 2019/1021 (2019).
