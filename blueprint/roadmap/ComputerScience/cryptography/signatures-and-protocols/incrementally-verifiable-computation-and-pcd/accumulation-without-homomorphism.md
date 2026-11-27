# Accumulation from non-homomorphic vector commitments

In the random oracle model there is an accumulation scheme for NP relations that uses only non-homomorphic vector commitments (for instance Merkle-tree commitments from a collision-resistant hash), by accumulating proximity claims of the form "the committed word is close to a codeword of a linear code satisfying a linear constraint" and spot-checking a few positions per accumulation. The scheme supports an a priori bounded number of accumulation steps (the distance parameter degrades with each step), and its security uses only symmetric-key primitives in the random oracle model, plausibly post-quantum. After heuristically instantiating the random oracle with a hash function, bounded-depth accumulation yields PCD for computation graphs of a priori bounded constant depth, which suffices for polynomial-length IVC through the tree construction of Bitansky–Canetti–Chiesa–Tromer.

## Proof sketch

A codeword-based claim is folded by a random linear combination of the two committed words; a proximity-gap style argument shows the combination is close to the code only if both inputs are, up to a small distance loss. The verifier checks consistency at a few random positions opened from the Merkle commitments, so no homomorphism is needed. Since each fold loses some distance, the number of supported steps is bounded in advance.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Merkle root](../../hash-functions/merkle-trees/root.md)
- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)

## Proof depends on

- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)
- [Existential soundness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Benedikt Bünz, Pratyush Mishra, Wilson Nguyen, William Wang, "Accumulation Without Homomorphism", ITCS (2025), IACR ePrint 2024/474, Sections 1.1 and 3.3.
- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013).
