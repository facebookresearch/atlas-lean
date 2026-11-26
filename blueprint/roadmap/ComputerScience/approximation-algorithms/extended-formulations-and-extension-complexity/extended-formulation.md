# Extended formulations and extension complexity

Let $K$ be a linearly ordered field and $P \subseteq K^d$. An **extended formulation** of $P$ is a system $Ex + Fy \le g$, $E'x + F'y = g'$ in the variables $x \in K^d$ and finitely many extra variables $y$ such that $x \in P$ if and only if some $y$ satisfies the system. Its **size** is the number of inequalities (equations are free). The **extension complexity** $\mathrm{xc}(P)$ is the minimum size of an extended formulation of $P$. For a polytope $P = \{x : Ax \le b\} = \mathrm{conv}\{v_1, \dots, v_N\}$, the **slack matrix** is $S_{ij} = b_i - A_i v_j \ge 0$.

## Depends on

- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- M. Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences 43(3), 1991.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
