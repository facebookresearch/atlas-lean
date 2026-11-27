# Segment-tree queries visit logarithmically many nodes

Build a [segment tree](build.md) from a list `xs` of length $n$ over an additive monoid. The empty list builds the empty tree, and a singleton list builds a leaf. For $n\ge 2$, the builder splits the list into a left half of length $\lfloor n/2\rfloor$ and the remaining right half. Let $h$ be `Nat.clog 2 n`: $\lceil\log_2 n\rceil$ for $n>0$, and zero for $n=0$.

**Theorem.**

1. The tree has height $h$, measuring height in edges and assigning height zero to the empty tree and to a leaf.
2. For any natural endpoints $l,r$, the [range query](query.md) makes at most four calls at each depth, at most $4h+1$ calls altogether, and at most $2h$ additions. Its result is the sum of `((xs.drop l).take (r - l))` in list order: the half-open range $[l,r)$ clamped to the list, with truncated natural subtraction. Calls that prune a subtree or use a cached aggregate count as visits. On the empty tree there is one call and no stored node is visited.
3. For a natural index $i<n$ and a replacement value $y$, the [point update](update.md) follows one root-to-leaf path. It makes at most $h+1$ calls and performs at most $h$ additions. The resulting leaf list is `xs.set i y`, with zero-based indices.

These bounds count calls and applications of the additive monoid operation, not allocation, copying, or elapsed time.

**Proof idea.** For $n\ge 2$ the larger child has length $\lceil n/2\rceil$, and the ceiling logarithm drops by one at that length. For a query, a call that descends has at least one query endpoint strictly inside its segment. Each endpoint can remain interior in at most one child, so at most two calls at a depth descend. Each such call visits both children and combines their results once. In particular, a child that returns zero can still count as a visit. A point update selects just one child at every internal call and recomputes one cached aggregate on return.

## Sources

- cp-algorithms, “Segment Tree”, <https://cp-algorithms.com/data_structures/segment_tree.html>: the logarithmic height, the argument bounding the number of vertices visited by a range query at each level, and the root-to-leaf traversal for a point update.
