# Well-separated pair decomposition

Let $s > 0$. Two disjoint finite sets $A, B \subset \mathbb{R}^d$ are *$s$-well separated* if they can be enclosed in two Euclidean balls of a common radius $r$ whose distance is at least $sr$. For sets $A$ and $B$ let $A \otimes B = \{\{a, b\} : a \in A, b \in B, a \ne b\}$. An *$s$-well separated pair decomposition* ($s$-WSPD) of a finite set $P \subset \mathbb{R}^d$ is a collection $\{\{A_1, B_1\}, \dots, \{A_m, B_m\}\}$ of pairs of subsets of $P$ such that $A_i \cap B_i = \emptyset$ and $A_i, B_i$ are $s$-well separated for each $i$, and $\bigcup_{i=1}^m A_i \otimes B_i = P \otimes P$. Its *size* is $m$.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 16, "Well Separated Pairs" and "Well Separated Pair Decomposition": $s$-well separated sets and conditions (1)–(4) of an $s$-WSPD
