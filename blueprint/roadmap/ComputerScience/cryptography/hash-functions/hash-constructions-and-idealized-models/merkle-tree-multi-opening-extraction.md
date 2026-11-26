# Extraction from multi-opening Merkle commitments

Let a Merkle tree over a collision-resistant hash commit to a table, and suppose an efficient prover outputs a root and, on request, openings (authentication paths) for positions of its choice that verify against the root. Then except with negligible probability (bounded by the collision-finding advantage), all verifying openings produced across any number of runs from the same root are consistent with a single table, which can be extracted from the openings. In the random oracle model the extraction is straight-line: the table is read off the adversary's oracle queries, with failure probability at most $O(q^2/2^n)$ for $q$ queries.

## Proof sketch

Two verifying openings of the same position with different leaf values give a collision on the first level where the recomputed paths agree. In the random oracle model, every node accepted by verification must have been queried, except with probability $q/2^n$, so the query log determines the tree.

## Depends on

- [Merkle root](../merkle-trees/root.md)
- [Merkle verifier](../merkle-trees/verify.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Constructive soundness of Merkle inclusion proofs](../merkle-trees/verify-sound-find-collision.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments", Proceedings of the 24th Annual ACM Symposium on Theory of Computing (STOC), 1992.
