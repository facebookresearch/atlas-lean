# The closest pair from a well-separated pair decomposition

Let $P$ be a set of $n \ge 2$ points in $\mathbb{R}^d$ and let $s > 2$. Take any $s$-WSPD of $P$, choose a representative point in each set of each pair, and return the pair of representatives at smallest distance. This is a closest pair of $P$: if $\{x, y\}$ is a closest pair and lies in $A \otimes B$, then $A = \{x\}$ and $B = \{y\}$, since any other point of $A$ would be within distance $2r < sr \le \|x - y\|$ of $x$. With the construction of a linear-size WSPD this computes the closest pair in $O(n \log n)$ time for fixed $d$.

## Depends on

- [Well-separated pair decomposition](well-separated-pair-decomposition.md)

## Proof depends on

- [Existence of linear-size well-separated pair decompositions](existence-of-linear-size-well-separated-pair-decompositions.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 17, "Closest Pair (Exact!)" and the argument that for $s > 2$ the closest representatives are the exact closest pair
