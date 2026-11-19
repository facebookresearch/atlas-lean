# Derivative of the Lagrangian

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. Here $E$ is a real normed space. If $f_0$ and every $f_i$ are Fréchet differentiable at $x$, then for every $\mu$ the map $y \mapsto L(y, \mu)$ is differentiable at $x$ with derivative $Df_0(x) + \sum_i \mu_i\, Df_i(x)$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.5.3, eq. (5.49) (stationarity condition).
