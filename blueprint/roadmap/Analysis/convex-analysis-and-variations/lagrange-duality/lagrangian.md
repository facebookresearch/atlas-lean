# Lagrangian

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. The **Lagrangian** of the problem is

$$L(x, \mu) = f_0(x) + \sum_{i \in \iota} \mu_i f_i(x), \qquad x \in E,\ \mu \in \mathbb{R}^\iota.$$

The $\mu_i$ are the Lagrange multipliers (Boyd–Vandenberghe write $\lambda_i$).

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.1.1 (without equality constraints).
