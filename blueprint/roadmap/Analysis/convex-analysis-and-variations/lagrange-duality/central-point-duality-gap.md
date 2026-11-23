# Duality gap of central points in the barrier method

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. Here $E$ is a real normed space and $m = |\iota|$. Suppose $f_0$ and every $f_i$ are convex on $D$ and differentiable at a strictly feasible $x \in D$ ($f_i(x) < 0$ for all $i$), let $t > 0$, and suppose $x$ satisfies the centrality condition

$$t\, Df_0(x) + \sum_i \frac{1}{-f_i(x)}\, Df_i(x) = 0,$$

i.e. $x$ is a stationary point of $t f_0 - \sum_i \log(-f_i)$, the objective the logarithmic barrier method minimizes. Then $\mu_i = -1/(t f_i(x))$ is dual feasible, $g(\mu) = f_0(x) - m/t$, and therefore $f_0(x) - m/t \le f_0(y)$ for every feasible $y$: the central point $x^\star(t)$ is at most $m/t$-suboptimal.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §11.2.2, eqs. (11.7)–(11.10) (without equality constraints).
