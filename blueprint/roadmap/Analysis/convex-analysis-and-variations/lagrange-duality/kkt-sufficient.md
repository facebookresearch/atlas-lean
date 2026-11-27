# Sufficiency of the KKT conditions for convex problems

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. Here $E$ is a real normed space. Suppose $f_0$ and every $f_i$ are convex on $D$ and differentiable at $x \in D$, and that $x$ and $\mu$ satisfy the **Karush–Kuhn–Tucker conditions**:

- primal feasibility: $f_i(x) \le 0$ for all $i$;
- dual feasibility: $\mu \ge 0$;
- complementary slackness: $\mu_i f_i(x) = 0$ for all $i$;
- stationarity: $Df_0(x) + \sum_i \mu_i\, Df_i(x) = 0$.

Then $f_0(x) \le f_0(y)$ for every feasible $y$, $g(\mu) = f_0(x)$ and $p^\star = f_0(x)$: $x$ is primal optimal and $\mu$ is dual optimal, with zero duality gap.

## Background

- [Karush–Kuhn–Tucker conditions for inequality constraints](../karush-kuhn-tucker-inequality.md): background, the converse direction, which shows the KKT conditions are necessary at a local minimizer under linear independence of the active constraint gradients, without convexity.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.5.3, "KKT conditions for convex problems" (without equality constraints).
