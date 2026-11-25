# Leaf pairs of a rooted binary tree with path lengths

The leaf pairs of a [rooted binary tree](rtree.md) form the list of quadruples (label, label, path length, number of edges): empty for a leaf; for an internal vertex with children $l, r$ on edges of lengths $a, b$, the pairs of $l$, the pairs of $r$, and for each [leaf](leaves.md) $(x, d, k)$ of $l$ and $(y, e, m)$ of $r$ the quadruple $(x, y, d + a + b + e, k + m + 2)$.
