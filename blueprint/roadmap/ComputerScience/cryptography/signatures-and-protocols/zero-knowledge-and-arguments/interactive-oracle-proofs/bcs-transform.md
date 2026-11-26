# The BCS transform

The *Ben-Sasson–Chiesa–Spooner (BCS) transform* compiles a public-coin IOP into a non-interactive argument in the random oracle model with two oracles, a Merkle hash $h$ and a Fiat–Shamir hash $H$. The prover commits to each IOP oracle $\pi_i$ by the root $\mathrm{rt}_i$ of a Merkle tree over its symbols (encoded as leaves), and derives the $i$-th challenge by chaining, $c_i = H(x, \mathrm{rt}_1, \dots, \mathrm{rt}_i)$ (or $H$ of the previous challenge and the new root). The proof consists of the roots and, for every position the IOP verifier queries, the symbol and its authentication path. The verifier recomputes the challenges, checks all paths and runs the IOP verifier on the opened symbols. Honest openings of an oracle table always pass Merkle verification, and the tables produced sequentially equal the IOP prover's oracles on the derived challenges.

## Depends on

- [Public-coin interactive oracle proofs](public-coin-iop.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Merkle root](../../../hash-functions/merkle-trees/root.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
