# Random oracles and LWE-based hashes are collapsing

(i) A random oracle $H:\{0,1\}^{n}\to\{0,1\}^{m}$ is collapsing against $q$-query adversaries, with distinguishing advantage $O(\sqrt{q^{3}/2^{m}})$. (ii) Assuming LWE (more generally, lossy functions), there are standard-model collapsing hash functions, for example built from lossy trapdoor functions or SIS-based hashes with a lossy mode, and Merkle trees of collapsing hashes are collapsing. (iii) Consequently statistically hiding, collapse-binding commitments and quantum-secure succinct arguments (Kilian's protocol with collapsing Merkle trees) exist under LWE.

## Proof sketch

For a random oracle, measuring $X$ versus not measuring it is indistinguishable unless the adversary's state contains a collision, whose probability is bounded by the compressed-oracle collision bound. For lossy-function constructions, in the lossy mode the hash is injective on a large structured set where measurement is implied, and indistinguishability of modes transfers collapsing. Collapsing composes along Merkle trees by a hybrid over levels.

## Depends on

- [Collapsing hash functions and collapse-binding commitments](collapsing-hash.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)
- [The quantum random oracle model](quantum-random-oracle-model.md)

## Proof depends on

- [Tight quantum query bound for finding collisions in a random function](qrom-collision-bound.md)

## Sources

- Dominique Unruh, "Computationally Binding Quantum Commitments", EUROCRYPT (2016), IACR ePrint 2015/361.
- Alessandro Chiesa, Fermi Ma, Nicholas Spooner, Mark Zhandry, "Post-Quantum Succinct Arguments: Breaking the Quantum Rewinding Barrier", FOCS (2021).
