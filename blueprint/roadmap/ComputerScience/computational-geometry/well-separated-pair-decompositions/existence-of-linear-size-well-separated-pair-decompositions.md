# Existence of linear-size well-separated pair decompositions

Let $P$ be a set of $n$ points in $\mathbb{R}^d$, for fixed $d$, and let $s \ge 1$. Then $P$ has an $s$-WSPD of size $O(s^d n)$, and one can be computed in $O(n \log n + s^d n)$ time from a compressed quadtree of $P$; in this construction every pair of $P$ lies in exactly one $A_i \otimes B_i$ (Callahan and Kosaraju).

## Depends on

- [Well-separated pair decomposition](well-separated-pair-decomposition.md)

## Proof depends on

- [Packing lemma for quadtree cells](packing-lemma-for-quadtree-cells.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 16, the theorem at the end of the lecture ($O(s^d n)$ pairs in $O(n \log n + s^d n)$ time) and its charging proof with the Packing Lemma
