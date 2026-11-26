# Ben-Or's lower bound for algebraic decision trees

For each $d \ge 1$ there is a constant $c_d > 0$ with the following property. Let $W \subseteq \mathbb{R}^N$ be a set with $M$ connected components and let $T$ be a $d$-th order algebraic decision tree that decides $W$. Then the height of $T$ is at least $c_d (\log_2 M - N)$.

## Depends on

- [Algebraic decision tree](algebraic-decision-tree.md)

## Proof depends on

- [Connected components of a basic semialgebraic set](connected-components-of-a-basic-semialgebraic-set.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the theorem attributed to Ben-Or: height $\Omega((\log M) - N)$ for a $d$-th order algebraic decision tree deciding a set with $M$ connected components
- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Section 5, Theorem 8 ($2^h \beta_d(n, h) \ge N$ for a $d$-th order decision tree of height $h$; hence $C_d(W) = \Omega(\log N - n)$ for fixed $d$)
