# Extraction from multi-opening Merkle commitments

Let a Merkle tree over a collision-resistant hash commit to a table, and suppose an efficient prover outputs a root and, on request, openings (authentication paths) for positions of its choice that verify against the root. Then except with negligible probability (bounded by the collision-finding advantage), all verifying openings produced across polynomially many runs from the same root are consistent with a single table, which can be extracted from the openings.

## Proof sketch

Two verifying openings of the same position with different leaf values give a collision on the first level where the recomputed paths agree.

## Depends on

- [Merkle root](../merkle-trees/root.md)
- [Merkle verifier](../merkle-trees/verify.md)

## Proof depends on

- [Constructive soundness of Merkle inclusion proofs](../merkle-trees/verify-sound-find-collision.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Section 8.9, Theorem 8.8.
- J. Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments", Proceedings of the 24th Annual ACM Symposium on Theory of Computing (STOC), 1992.
