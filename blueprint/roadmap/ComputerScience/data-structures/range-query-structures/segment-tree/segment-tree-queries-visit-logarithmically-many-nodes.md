# Segment-tree queries visit logarithmically many nodes

Let $t$ be a balanced [segment tree](segment-tree.md) over an array of length $n$. Each node stores the aggregate, under an associative operation, of its segment, and its two children split that segment in half.

**Theorem.**
1. The tree has height $\lceil \log_2 n \rceil$.
2. A [range query](query.md) over $[l, r)$ visits at most four nodes on each level, hence $O(\log n)$ nodes, and returns the aggregate of the range using $O(\log n)$ applications of the operation.
3. A point update changes the $O(\log n)$ nodes on one root-to-leaf path.

**Proof.** The segment lengths halve on each level, which gives part 1. For part 2, use induction on the level. Every visited node whose segment is neither disjoint from $[l, r)$ nor contained in it must contain $l$ or $r$ in its interior. At most two nodes per level do, and only those two recurse. So at most four nodes are visited on the next level.

## Depends on

- [Segment tree](segment-tree.md)
- [Range query on a segment tree](query.md)

## Sources

- cp-algorithms, "Segment Tree", <https://cp-algorithms.com/data_structures/segment_tree.html>: the height $O(\log n)$, the sum query in $O(\log n)$ time with the inductive proof that each level has at most four visited vertices, and point update in $O(\log n)$.
