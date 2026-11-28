# Saddle points of the Lagrangian are primal–dual optimal pairs

Consider minimizing $f_0(x)$ over $x \in D$ subject to $f_i(x) \le 0$ for $i$ in a finite index set, with Lagrangian $L(x, \lambda) = f_0(x) + \sum_i \lambda_i f_i(x)$ for $\lambda \ge 0$. A pair $(x^\star, \lambda^\star)$ with $x^\star \in D$ and $\lambda^\star \ge 0$ is a saddle point, $L(x^\star, \lambda) \le L(x^\star, \lambda^\star) \le L(x, \lambda^\star)$ for all $x \in D$ and $\lambda \ge 0$, if and only if $x^\star$ is primal optimal, $\lambda^\star$ is dual optimal and the primal and dual optimal values are equal and finite. No convexity is assumed.

Proof. Suppose $(x^\star, \lambda^\star)$ is a saddle point. If some $f_i(x^\star) > 0$, letting $\lambda_i \to \infty$ violates the left inequality, so $x^\star$ is feasible; taking $\lambda = 0$ gives $\sum_i \lambda^\star_i f_i(x^\star) \ge 0$, hence $= 0$ and $L(x^\star, \lambda^\star) = f_0(x^\star)$. The right inequality says that the dual function at $\lambda^\star$ equals $L(x^\star, \lambda^\star) = f_0(x^\star)$, so by weak duality $x^\star$ and $\lambda^\star$ are optimal with zero gap. Conversely, if $x^\star$ is feasible and $f_0(x^\star)$ equals the dual function at $\lambda^\star$, then that value is at most $L(x^\star, \lambda^\star) = f_0(x^\star) + \sum_i \lambda^\star_i f_i(x^\star) \le f_0(x^\star)$, so all are equal: this is the right inequality, and $L(x^\star, \lambda) \le f_0(x^\star) = L(x^\star, \lambda^\star)$ for every $\lambda \ge 0$ is the left one.

## Depends on

- [Lagrangian](lagrangian.md): the Lagrangian.
- [Lagrange dual function](dual-function.md): the Lagrange dual function.

## Proof depends on

- [Weak duality](dual-value-le-primal-value.md): weak duality.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.4.2 (saddle-point interpretation)
