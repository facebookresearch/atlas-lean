# Spanners from well-separated pair decompositions

Let $P$ be a set of $n$ points in $\mathbb{R}^d$, for fixed $d$, and let $t > 1$. Take an $s$-WSPD of $P$ of size $O(s^d n)$, as given by the existence theorem, with $s = 4(t+1)/(t-1)$, and for each pair $\{A_i, B_i\}$ add one edge between a representative of $A_i$ and a representative of $B_i$. The resulting graph is a $t$-spanner for $P$ with $O(s^d n)$ edges, and it can be built in $O(n \log n + s^d n)$ time.

## Depends on

- [Well-separated pair decomposition](well-separated-pair-decomposition.md)
- [Geometric spanner](geometric-spanner.md)

## Proof depends on

- [Existence of linear-size well-separated pair decompositions](existence-of-linear-size-well-separated-pair-decompositions.md)
- [Distances within a well-separated pair](distances-within-a-well-separated-pair.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 17, "WSPD-based Spanner Construction" with $s = 4(t+1)/(t-1)$, and its correctness proof by induction
