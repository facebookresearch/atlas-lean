# Kilian's protocol is an argument of knowledge

For a collision-resistant hash family and a polynomial-time PCP verifier with $O(\log |x|)$ random bits, there is a strict probabilistic polynomial-time rewinding extractor which, given a cheating prover that convinces the verifier with probability $\varepsilon$, runs it on independent PCP challenges and assembles a compact PCP table from the opened positions; either the table is accepted by the PCP verifier on a large fraction of random strings, so that a witness can be decoded by the PCP's knowledge (proof-of-knowledge) property, or two runs open a common position differently and yield a hash collision. Running $R$ independent extraction trials shrinks the failure probability to its $R$-th power, so for every polynomial $p$ and prover with $\varepsilon \ge 1/p$, extraction succeeds with overwhelming probability, except for the collision-finding advantage.

## Proof sketch

Every accepted run reveals at most polylogarithmically many table positions; since the verifier uses logarithmic randomness, polynomially many rewinds cover all random strings, and consistency across runs is guaranteed unless the Merkle tree is opened inconsistently.

## Depends on

- [Succinct arguments from probabilistically checkable proofs](../succinct-arguments-from-probabilistically.md)
- [Knowledge soundness](../knowledge-soundness.md)

## Proof depends on

- [Soundness of Kilian's protocol from Merkle position binding](kilian-exact-soundness.md)

## Sources

- Joe Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments (Extended Abstract)", Proceedings of the Twenty-Fourth Annual ACM Symposium on Theory of Computing, 1992.
- Boaz Barak and Oded Goldreich, "Universal Arguments and their Applications", Electronic Colloquium on Computational Complexity, 2001.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
