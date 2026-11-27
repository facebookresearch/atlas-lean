# Ben-Or's lower bound for algebraic decision trees

Let $d \ge 1$ and $N \ge 1$, let $W \subseteq \mathbb{R}^N$ be a set with $M \ge 1$ connected components, and let $T$ be a $d$-th order algebraic decision tree of height $h$ that decides $W$. Then

$$3^h \, d\,(2d-1)^{N+h-1} \ge M, \qquad\text{so}\qquad h \ge \frac{\log_2 M - (N-1)\log_2(2d-1) - \log_2 d}{\log_2 3 + \log_2(2d-1)} .$$

Indeed the inputs reaching a leaf satisfy at most $h$ polynomial sign conditions of degree at most $d$, so each leaf set has at most $d(2d-1)^{N+h-1}$ connected components, every component of $W$ contains a component of some leaf set, and there are at most $3^h$ leaves. Hence for fixed $d$ there are constants $a_d, b_d > 0$ with $h \ge a_d \log_2 M - b_d N$. This is often written $\Omega(\log M - N)$, but the coefficient of $N$ cannot be taken equal to that of $\log_2 M$: for $d = 6$ the set $W = \{0, 1, 2\}^N$ has $3^N$ components and is decided by the single test $\sum_{i=1}^N [x_i(x_i - 1)(x_i - 2)]^2 = 0$.

## Depends on

- [Algebraic decision tree](algebraic-decision-tree.md)

## Proof depends on

- [Connected components of a basic semialgebraic set](connected-components-of-a-basic-semialgebraic-set.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the theorem attributed to Ben-Or, stated there as height $\Omega((\log M) - N)$ for a $d$-th order algebraic decision tree deciding a set with $M$ connected components
- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Section 5, Theorem 8 ($2^h \beta_d(n, h) \ge N$ for a $d$-th order decision tree of height $h$, with two-way tests) and Section 3, Theorem 2 ($\beta_d(n, h) \le d(2d-1)^{n+h-1}$, stated for $d \ge 2$; for $d = 1$ each leaf set is convex, with at most one component, which the displayed bound covers), which give the explicit bound above
