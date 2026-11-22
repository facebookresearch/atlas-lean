# The Su–Boyd–Candès rate for the continuous limit of Nesterov's method

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ convex and differentiable with a global minimizer $x^\star$, and $t_0 > 0$. If $X, V : \mathbb{R} \to E$ satisfy $\dot X_t = V_t$ and $\dot V_t = -\frac{3}{t}V_t - \nabla f(X_t)$ for every $t \ge t_0$, that is

$$
\ddot X_t + \frac{3}{t}\dot X_t + \nabla f(X_t) = 0 \quad (t \ge t_0),
$$

then for every $t \ge t_0$

$$
f(X_t) - f(x^\star) \le \frac{2\,\|X_{t_0} + \tfrac{t_0}{2} V_{t_0} - x^\star\|^2 + t_0^2\bigl(f(X_{t_0}) - f(x^\star)\bigr)}{t^2} .
$$

The equation is (3.2) of Wibisono, Wilson and Jordan with $p = 2$, $C = 1/4$ and $\nabla^2 h = I$, which they identify with the differential equation of Su, Boyd and Candès; the bound is the case $p = 2$ of the [polynomial rate](polynomial-family-rate.md), with $Z_t = X_t + \frac{t}{2}\dot X_t$. The statement starts at $t_0 > 0$, avoiding the singularity of the damping $3/t$ at $t = 0$.

## Informally uses

- [Polynomial rate for the polynomial Bregman-Lagrangian family](polynomial-family-rate.md): the case $p = 2$, $C = 1/4$.

## Background

- [Nesterov's $O(1/k^2)$ rate](nesterov-accelerated-rate.md): the discrete method whose limit this equation is.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), Section 3 (equation (3.2) and the identification with Su et al.).
- W. Su, S. Boyd and E. J. Candès, *A differential equation for modeling Nesterov's accelerated gradient method: theory and insights*, J. Mach. Learn. Res. 17 (2016).
