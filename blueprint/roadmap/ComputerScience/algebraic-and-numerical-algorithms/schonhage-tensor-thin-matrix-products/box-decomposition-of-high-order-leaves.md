# Disjoint box decomposition of high-order leaves

For an output with $m$ inner levels and threshold $t \le m$, padding the $P_0$ levels of each contributing leaf of order at least $t$ from below yields a unique box containing it. Boxes indexed by different level sets are disjoint, their leaf sets partition exactly the contributing leaves of order at least $t$, and each box is determined by its unique contributing leaf of order exactly $t$. Hence each queried product entry equals a sum of retained box values plus an explicit sum over the low-order leaves.

## Depends on

- [Boxes of tensor leaves](boxes-of-tensor-leaves.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
