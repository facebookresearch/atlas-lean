# Convex KKT conditions are sufficient

Let $E$ be a real normed space, and let $f$ and $g_1, \dots, g_m$ be convex on $E$ and differentiable at $x$. Suppose the multipliers satisfy $\lambda_i \ge 0$, complementary slackness $\lambda_i g_i(x) = 0$, and stationarity $Df(x) + \sum_i \lambda_i Dg_i(x) = 0$. Then $f(x) \le f(y)$ for every $y$ with $g_i(y) \le 0$ for all $i$. Feasibility of $x$ is not needed for this bound; when $x$ is feasible it is a global minimizer on the feasible set. No constraint qualification is needed.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3.
