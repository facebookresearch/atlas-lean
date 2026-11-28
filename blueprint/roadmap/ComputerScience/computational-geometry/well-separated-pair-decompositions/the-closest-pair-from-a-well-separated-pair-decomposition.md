# The closest pair from a well-separated pair decomposition

Let $P$ be a set of $n \ge 2$ points in $\mathbb{R}^d$ and let $s > 2$. Take any $s$-WSPD of $P$ whose pairs have nonempty sides, choose a representative point in each set of each pair, and return the pair of representatives at smallest distance. This is a closest pair of $P$: a closest pair $\{x, y\}$ lies in $A \otimes B$ for some pair $\{A, B\}$; naming its sides so that $x \in A$ and $y \in B$, we get $A = \{x\}$ and $B = \{y\}$, since any other point of $A$ would be within distance $2r < sr \le \|x - y\|$ of $x$, and symmetrically for $B$. With the WSPD of size $O(s^d n)$ given by the existence theorem, this takes $O(n \log n + s^d n)$ time for fixed $d$, hence $O(n \log n)$ for a fixed $s$ such as $s = 3$.

## Depends on

- [Well-separated pair decomposition](well-separated-pair-decomposition.md)

## Proof depends on

- [Existence of linear-size well-separated pair decompositions](existence-of-linear-size-well-separated-pair-decompositions.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 17, "Closest Pair (Exact!)" and the argument that for $s > 2$ the closest representatives are the exact closest pair
