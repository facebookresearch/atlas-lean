# Polynomial rate $O(1/t^p)$ for the polynomial Bregman-Lagrangian family (Euclidean case)

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ convex and differentiable with a global minimizer $x^\star$, and $p, C, t_0 > 0$. Let $X, Z : \mathbb{R} \to E$ satisfy, for every $t \ge t_0$,

$$
Z_t = X_t + \tfrac{t}{p}\dot X_t, \qquad \dot Z_t = -C p\, t^{p-1}\,\nabla f(X_t)
$$

(the first written as $\dot X_t = \frac{p}{t}(Z_t - X_t)$). Then for every $t \ge t_0$,

$$
f(X_t) - f(x^\star) \le \frac{\tfrac12\|Z_{t_0} - x^\star\|^2 + C t_0^p\bigl(f(X_{t_0}) - f(x^\star)\bigr)}{C\, t^p} .
$$

This is the system (3.3a)–(3.3b) of Wibisono, Wilson and Jordan for $h = \|\cdot\|^2/2$, equivalent to the second-order equation (3.2) $\ddot X_t + \frac{p+1}{t}\dot X_t + C p^2 t^{p-2}\nabla f(X_t) = 0$; it is the Euler–Lagrange equation of the Bregman Lagrangian with $\alpha_t = \log p - \log t$, $\beta_t = p\log t + \log C$ (3.1a)–(3.1b), which satisfy the ideal scaling with equality. The case $p = 2$ is the continuous-time limit of Nesterov's method, and $p = 3$ that of accelerated cubic-regularized Newton.

## Informally uses

- [Convergence rate of the Bregman-Lagrangian flow](bregman-lagrangian-rate.md): applied with $e^{\alpha_t} = p/t$ and $e^{\beta_t} = C t^p$.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), Section 3, equations (3.1)–(3.3).
