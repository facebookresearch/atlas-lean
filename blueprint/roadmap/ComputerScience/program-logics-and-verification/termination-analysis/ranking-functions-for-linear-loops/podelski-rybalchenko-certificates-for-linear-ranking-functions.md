# Podelski–Rybalchenko certificates for linear ranking functions

Consider a single-path [linear-constraint loop](linear-constraint-loops.md) over rational variables $x = (x_1, \dots, x_n)$ whose transitions $(x, x')$ are exactly the solutions of

$$A x + A' x' \le b,$$

with $A$, $A'$ rational $(r+s) \times n$ matrices and $b \in \mathbb{Q}^{r+s}$ (the first $r$ rows, with zero $A'$ part, being the loop condition), and assume this system is satisfiable. Then the loop has a [linear ranking function](linear-ranking-functions.md) if and only if there are vectors $\lambda_1, \lambda_2 \in \mathbb{Q}^{r+s}$ with $\lambda_1, \lambda_2 \ge 0$ and

$$\lambda_1^\top A' = 0, \qquad (\lambda_1^\top - \lambda_2^\top) A = 0, \qquad \lambda_2^\top (A + A') = 0, \qquad \lambda_2^\top b < 0 .$$

For every such pair, $x \mapsto \lambda_2^\top A' x$ is the linear part of a linear ranking function, and every linear ranking function arises from such a pair. Since the conditions form a linear program, existence of a linear ranking function for such a loop is decidable in polynomial time.

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Linear ranking functions](linear-ranking-functions.md)

## Proof depends on

- [Farkas' lemma for inequality systems](../../../../Geometry/convex-geometry/linear-programming/exists-nonneg-mul-vec-le-iff.md)

## Sources

- R. Bagnara, F. Mesnard, A. Pescetti and E. Zaffanella, "The automatic synthesis of linear ranking functions: the complete unabridged version", arXiv:1004.0944v2, 2012, <https://arxiv.org/abs/1004.0944v2>, Section 5 (the method of Podelski and Rybalchenko, conditions (37a)–(37d) and the ranking function (38)), Theorem 4.4 and Theorem 6.1 (the ranking functions obtained by the method are exactly the linear ranking functions), and Corollary 4.5 (polynomial time).
