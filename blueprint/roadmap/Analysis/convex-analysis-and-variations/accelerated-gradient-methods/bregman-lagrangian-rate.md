# Convergence rate of the Bregman-Lagrangian flow (Euclidean case)

Under the hypotheses of [the energy monotonicity theorem](bregman-lagrangian-energy-antitone-on.md) (convex differentiable $f$ with minimizer $x^\star$, ideal scaling $\dot\beta_t \le e^{\alpha_t}$, and $\dot X_t = e^{\alpha_t}(Z_t - X_t)$, $\dot Z_t = -e^{\alpha_t+\beta_t}\nabla f(X_t)$ for $t \ge t_0$), for every $t \ge t_0$

$$
f(X_t) - f(x^\star) \le \mathcal E_{t_0}\, e^{-\beta_t}, \qquad
\mathcal E_{t_0} = \tfrac12\|Z_{t_0} - x^\star\|^2 + e^{\beta_{t_0}}\bigl(f(X_{t_0}) - f(x^\star)\bigr).
$$

That is, $f(X_t) - f(x^\star) = O(e^{-\beta_t})$; with $\dot\beta = e^\alpha$ the rate is $O(\exp(-\int_{t_0}^t e^{\alpha_s}\,ds))$.

## Informally uses

- [The energy of the Bregman-Lagrangian flow is nonincreasing](bregman-lagrangian-energy-antitone-on.md): $e^{\beta_t}(f(X_t) - f(x^\star)) \le \mathcal E_t \le \mathcal E_{t_0}$.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), Theorem 2.1 (the final bound of its proof).
