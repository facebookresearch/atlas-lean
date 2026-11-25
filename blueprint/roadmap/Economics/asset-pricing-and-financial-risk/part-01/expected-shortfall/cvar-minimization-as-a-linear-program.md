# CVaR minimization over finitely many scenarios as a linear program

Let $X$ be a nonempty polyhedron of decisions, scenario probabilities $p_s \ge 0$ with $\sum_s p_s = 1$, losses $L_s(x)$ affine in $x$, and $0 \le \alpha < 1$. Define $\mathrm{CVaR}_\alpha(L(x)) = \min_z F(x, z)$ with $F(x, z) = z + (1-\alpha)^{-1}\sum_s p_s (L_s(x) - z)_+$; the minimum over $z$ exists for each $x$. Then $\inf_{x \in X}\mathrm{CVaR}_\alpha(L(x))$ equals the infimum of the linear program minimizing $z + (1-\alpha)^{-1}\sum_s p_s u_s$ over $x \in X$, $z$ and $u$ subject to $u_s \ge 0$ and $u_s \ge L_s(x) - z$. A decision $x$ minimizes $\mathrm{CVaR}_\alpha(L(x))$ over $X$ exactly when $(x, z, u)$ is optimal in the linear program for some $z$ and $u$; for such an optimal point, $z$ minimizes $F(x, \cdot)$ and $u_s = (L_s(x) - z)_+$ for every scenario with $p_s > 0$, while $u_s$ is only constrained by $u_s \ge \max(0, L_s(x) - z)$ when $p_s = 0$.

## Sources

- R. T. Rockafellar and S. Uryasev, "Optimization of conditional value-at-risk", *Journal of Risk* 2(3):21–41, 2000, Theorems 1–2, the sample approximation (9) and the linear reformulation following (17)
