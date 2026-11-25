# Orthogonal range reporting with range trees

Let $P$ be a set of $n$ points in $\mathbb{R}^d$. A one-dimensional [range tree](range-tree.md) is a balanced search tree on the coordinates. A $d$-dimensional range tree is a balanced search tree on the first coordinate in which every node also stores a $(d - 1)$-dimensional range tree of the points in its subtree, on the remaining coordinates.

**Theorem.**
1. A $d$-dimensional range tree uses $O(n\log^{d-1} n)$ space. It reports the $k$ points inside an axis-parallel box in $O(\log^d n + k)$ time.
2. *Layered range trees* replace the last level by sorted arrays with *fractional-cascading* pointers from each node's array into its children's arrays. For $d \ge 2$ they reduce the query time to $O(\log^{d-1} n + k)$, with the same space; in the plane this gives $O(\log n + k)$. In one dimension the range tree itself answers queries in $O(\log n + k)$ time.

**Proof.**
1. A query in the first coordinate selects $O(\log n)$ canonical subtrees whose union is exactly the points in the range. The query then recurses into the $(d - 1)$-dimensional structure of each, giving $O(\log^d n)$ search time plus $O(k)$ for output. Each point appears in $O(\log n)$ structures per level of nesting.
2. In the last dimension, the position of the query interval in a child's array is found in $O(1)$ time from the parent's position by following a pointer, instead of by binary search. This saves one factor of $\log n$.

## Depends on

- [Range tree](range-tree.md)

## Background

- [Fractional cascading](../fractional-cascading/README.md)
- [Orthogonal range reporting in a kd-tree](../k-d-tree/orthogonal-range-reporting-in-a-kd-tree.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 3 "Geometric structures" (scribe notes, 23 February 2012), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec3.pdf>:
    - Section 3.1: range trees in one dimension, two-dimensional range trees with a $y$-range tree at every $x$-node, $O(n\log n)$ space and $O(\log^2 n)$ query time, and $O(\log^d n)$ in $d$ dimensions;
    - Section 3.2: layered range trees with $O(\log^{d-1} n)$ query time;
    - Section 4: fractional cascading.
