# Adler's Dantzig game of a linear feasibility problem

The *linear feasibility problem* $F(A, b)$ for $A \in K^{m \times n}$, $b \in K^m$ asks for $x \ge 0$ with $Ax = b$, or a proof that none exists. Writing $Ax = b$ as $b \le Ax$ together with $\sum_i (Ax)_i \le \sum_i b_i$, the *Dantzig game associated with $F(A,b)$* is the Dantzig game of the auxiliary program

$$
\min\Bigl\{u : b \le Ax + u\mathbf{1},\ \textstyle\sum_i (Ax)_i - u \le \sum_i b_i,\ x \ge 0,\ u \ge 0\Bigr\},
$$

with strategies $(y, v, x, u, t)$. Its solutions resolve $F(A,b)$ unless $t = 0$: if $t > 0$ and $u = 0$ then $x/t$ solves $F(A,b)$; if $u > 0$ then $y - v\mathbf{1}$ certifies infeasibility; if $t = 0$ then $x$ is a nonzero solution of $Ax = 0$, $x \ge 0$. The *bounded problem* $F(\hat A, \hat b(\beta))$ adds a slack $s \ge 0$ and the constraint $\sum_j x_j + s = \beta$.

## Depends on

- [Dantzig's symmetric game of a linear program](dantzig-game.md)
- [Exists nonneg mul Vec eq iff](../../../Geometry/convex-geometry/linear-programming/exists-nonneg-mul-vec-eq-iff.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
