# Routed box products with one shared box geometry

There is a deterministic word-RAM program that, given matrices $A \in \mathbb{Z}^{N \times D}$, $B \in \mathbb{Z}^{D \times N}$, raw query positions and a threshold, computes all queried entries of $AB$ by routing queries to tiles, building the box geometry once, building each tile's retained box values, and answering each tile's queries by sparse box queries, then restoring the queries to their original order and the input to its original state. At the block parameters of the box trade-off its instruction count is $O\big(\mathrm{poly}(m) \cdot N^2 D^{-0.064}\big)$ plus a linear charge per query occurrence.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Boxes of tensor leaves](boxes-of-tensor-leaves.md)

## Proof depends on

- [The box preprocessing/query trade-off and the exponent 0.064](box-tradeoff-exponent.md)
- [Disjoint box decomposition of high-order leaves](box-decomposition-of-high-order-leaves.md)
- [Queried thin matrix products in sub-output time](queried-thin-matrix-products.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
