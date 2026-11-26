# Ben-Or's lower bound for algebraic decision trees

For each $d \ge 1$ there is a constant $c_d > 0$ with the following property. Let $W \subseteq \mathbb{R}^N$ be a set with $M$ connected components and let $T$ be a $d$-th order algebraic decision tree that decides $W$. Then the height of $T$ is at least $c_d (\log_2 M - N)$.

## Depends on

- [Algebraic decision tree](algebraic-decision-tree.md)

## Expansion

This page becomes ready once:

- Proof prerequisite: the Milnor–Thom bound on the number of connected components of a real semi-algebraic set defined by polynomial sign conditions, which Ben-Or's argument applies to the sets of inputs reaching each leaf.
- Source check: the original paper (M. Ben-Or, "Lower bounds for algebraic computation trees", 1983) has not been opened; the page follows the lecture notes cited below.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the theorem attributed to Ben-Or: height $\Omega((\log M) - N)$ for a $d$-th order algebraic decision tree deciding a set with $M$ connected components
