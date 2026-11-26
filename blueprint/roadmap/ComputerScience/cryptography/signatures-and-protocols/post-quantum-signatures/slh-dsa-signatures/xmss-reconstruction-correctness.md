# Correctness of XMSS public-key reconstruction

For every XMSS tree and leaf index $idx < 2^{h'}$, reconstructing from an honest WOTS+ signature for leaf $idx$ and its authentication path returns the root of the tree. After $j$ iterations the address used is the tree address of the input's layer and tree with height $j$ and index $\lfloor idx / 2^j \rfloor$.

## Proof sketch

Induct on $j$: the current node equals the tree node at height $j$ above the leaf, and one $\mathbf{H}$ call with the sibling in the correct order gives the parent. The base case is WOTS+ correctness.

## Depends on

- [XMSS trees and authentication paths in SLH-DSA](xmss-trees.md)

## Proof depends on

- [Correctness of WOTS+ public-key reconstruction](wots-plus-correctness.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- National Institute of Standards and Technology, "Stateless Hash-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
