# Hardness assumptions

## A counting lemma

- [Comparing tests on uniform samples](win-prob-map-uniform-le-of-equiv.md)

## Discrete logarithm and computational Diffie–Hellman

- [Discrete-logarithm experiment](dlog-game.md)
- [Discrete-logarithm advantage](dlog-advantage.md)
- [Computational Diffie–Hellman experiment](cdh-game.md)
- [CDH advantage](cdh-advantage.md)
- [CDH solver from a discrete-logarithm solver](cdh-of-dlog.md)
- [CDH hardness implies discrete-logarithm hardness](dlog-advantage-le-cdh-advantage.md)
- [DDH distinguisher from a CDH solver](ddh-of-cdh.md)
- [On real triples the distinguisher runs the CDH experiment](ddh-real-ddh-of-cdh.md)
- [The CDH-based distinguisher on random triples](win-prob-ddh-rand-ddh-of-cdh.md)
- [DDH advantage of the distinguisher built from a CDH solver](ddh-advantage-ddh-of-cdh.md)
- [DDH hardness implies CDH hardness](cdh-advantage-le-ddh-advantage.md)
- [DDH hardness implies discrete-logarithm hardness](dlog-advantage-le-ddh-advantage.md)

## RSA and factoring

- [RSA-inversion experiment](rsa-game.md)
- [RSA-inversion advantage](rsa-advantage.md)
- [Nontrivial factorization](is-factorization.md)
- [Factoring experiment](factor-game.md)
- [Factoring advantage](factor-advantage.md)
- [Factorizations of a product of two primes](eq-or-eq-of-mul-eq.md)
- [Modular inverse of an exponent](mul-inv-val-mod-eq.md)
- [RSA inverter from a factoring algorithm](rsa-of-factor.md)
- [The inverse exponent inverts RSA encryption](pow-inv-val-pow.md)
- [Correctness of the reduction from RSA to factoring](rsa-of-factor-pow-e.md)
- [RSA hardness implies factoring hardness](factor-advantage-le-rsa-advantage.md)

- [RSA inversion versus factoring](rsa-inversion-versus-factoring.md)

## Key-indexed trapdoor functions

The variable-time definitions use [exact fair-bit sampling with a running-time tail](../../security-games/fair-bit-sampling-with-a-running-time-tail/README.md).

- [Index](index-2.md)
- [Data of a key-indexed trapdoor family](family.md)
- [Generated](generated.md)
- [Trapdoor correctness at matching keys](correct-at.md)
- [Finite-domain inverse laws](bij-on-and-right-inv-on.md)
- [Deterministic operations of a trapdoor family](deterministic-core.md)
- [Variable-time trapdoor function scheme](variable-time-trapdoor-function-scheme.md)
- [Trapdoor permutations](trapdoor-permutations.md)
- [One-way experiment on a public transcript](transcript-game.md)
- [One-wayness against variable-time public-transcript algorithms](is-transcript-one-way.md)
- [One-wayness against efficient interactive adversaries](interactive-one-wayness.md)

## Bounded-coin schemes

- [Bounded-coin trapdoor function scheme](is-bounded-coin-function-scheme.md)
- [Nonempty bounded-coin domains](bounded-coin-domain-nonempty.md)
- [A restriction of exact bounded-coin sampling](bounded-coin-domain-cardinality.md)
- [Bounded-coin trapdoor permutation scheme](is-bounded-coin-permutation-scheme.md)
- [The bounded-coin one-way experiment](bounded-coin-one-way-game.md)
- [Bounded-coin one-wayness](is-bounded-coin-one-way.md)

## Further hardness assumptions and constructions

- [Learning with errors](learning-with-errors.md)
- [Black-box constructions and oracle separations](black-box-constructions-and-oracle-separations.md)
- [Regev's public-key encryption from learning with errors](regev-s-public-key-encryption-from-learning.md)
- [No relativizing construction of key agreement from one-way permutations](no-relativizing-construction-of-key-agreement.md)
- [Shoup's generic lower bound for discrete logarithms](shoup-s-generic-lower-bound-for-discrete.md)
