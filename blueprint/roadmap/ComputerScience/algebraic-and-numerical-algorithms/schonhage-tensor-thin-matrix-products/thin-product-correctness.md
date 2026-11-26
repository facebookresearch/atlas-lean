# Exact queried entries of thin products via tiling

Let $A$ be an $N \times D$ and $B$ a $D \times N$ signed integer matrix, with $D = 4^m$. Pad and tile the outer dimension into bands of size $7^{\ell}$ and assign level sets of size $m$ to block pairs by a valid layout. Then for every queried position $(i, j)$, the pruned tensor evaluation on the band arrays returns exactly $(AB)_{ij}$, for arbitrary signed entries and any valid layout; band encodings are shared across tiles, and the number of encoding entries, contributing leaves and passed sets are bounded explicitly.

## Depends on

- [Leaves of the tensor power and their order](tensor-power-leaves-and-order.md)

## Proof depends on

- [Pruned evaluation of the tensor recursion](pruned-tensor-evaluation.md)
- [Schönhage's ten-term polynomial identity with error term](schonhage-ten-term-identity.md)
- [Sparse query bound for contributing leaves](sparse-leaf-bound.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
