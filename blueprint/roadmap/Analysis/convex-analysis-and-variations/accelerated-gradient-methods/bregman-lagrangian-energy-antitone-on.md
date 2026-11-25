# The energy of the Bregman-Lagrangian flow is nonincreasing (Euclidean case)

Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$ convex and differentiable with a global minimizer $x^\star$. Let $\alpha, \beta : \mathbb{R} \to \mathbb{R}$ and $X, Z : \mathbb{R} \to E$, and $t_0 \in \mathbb{R}$. Suppose that at every $t \ge t_0$, $\beta$ is differentiable with the ideal scaling $\dot\beta_t \le e^{\alpha_t}$ (eq. (2.2a)), and

$$
\dot X_t = e^{\alpha_t}(Z_t - X_t), \qquad \dot Z_t = -e^{\alpha_t + \beta_t}\,\nabla f(X_t).
$$

The first equation says $Z = X + e^{-\alpha}\dot X$; the second is the Euler–Lagrange equation (2.7) $\frac{d}{dt}\nabla h(X_t + e^{-\alpha_t}\dot X_t) = -e^{\alpha_t+\beta_t}\nabla f(X_t)$ for $h = \|\cdot\|^2/2$. Then the [energy](energy.md) $\mathcal E_t = \tfrac12\|Z_t - x^\star\|^2 + e^{\beta_t}(f(X_t) - f(x^\star))$ is nonincreasing on $[t_0, \infty)$.

Proof: $\dot{\mathcal E}_t = -e^{\alpha_t+\beta_t}\bigl(f(x^\star) - f(X_t) - \langle\nabla f(X_t), x^\star - X_t\rangle\bigr) + (\dot\beta_t - e^{\alpha_t})e^{\beta_t}(f(X_t) - f(x^\star))$; the first term is $\le 0$ by convexity, the second by the ideal scaling and minimality of $x^\star$.

The second ideal-scaling condition $\dot\gamma = e^\alpha$ (2.2b) is what reduces the Euler–Lagrange equation (2.5) of the Bregman Lagrangian $\mathcal L(X, V, t) = e^{\alpha_t+\gamma_t}(D_h(X + e^{-\alpha_t}V, X) - e^{\beta_t}f(X))$ to (2.7); the theorem is stated directly for solutions of (2.7), as in the paper. The statement concerns the Euclidean case.

## Informally uses

- [First-order condition for convexity](../first-order-conditions-for-convexity/add-fderiv-le-of-convex-on.md): nonnegativity of the Bregman divergence of $f$, $f(x^\star) - f(X_t) - \langle\nabla f(X_t), x^\star - X_t\rangle \ge 0$.

## Background

- [Euler–Lagrange equation](../euler-lagrange-equation/README.md): the variational principle that produces (2.5)–(2.7) from the Bregman Lagrangian.
- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/README.md): Lyapunov functions for autonomous systems; here the Lyapunov function is time-dependent.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), Theorem 2.1 and its proof.
