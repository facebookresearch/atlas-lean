# Convex KKT conditions with affine equalities are sufficient

Minimize $f$ subject to $g_i(y) \le 0$ ($i < m$) and $h_j(y) = 0$ ($j < p$) on a real normed space, where $f$ and every $g_i$ are convex, every $h_j$ is affine (convex and concave), and all are differentiable at $x$. Suppose $h_j(x) = 0$ for all $j$, and there are $\lambda_i \ge 0$ and real $\mu_j$ with complementary slackness $\lambda_i g_i(x) = 0$ and stationarity

$$Df(x) + \sum_i \lambda_i\,Dg_i(x) + \sum_j \mu_j\,Dh_j(x) = 0.$$

Then $f(x) \le f(y)$ for every feasible $y$. The inequality constraints need not hold at $x$, and no constraint qualification is needed.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3.
