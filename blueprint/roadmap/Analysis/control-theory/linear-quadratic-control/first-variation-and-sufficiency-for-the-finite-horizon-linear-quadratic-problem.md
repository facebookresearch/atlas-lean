# First variation and sufficiency for the finite-horizon linear-quadratic problem

Let $T > 0$, let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$, let $Q, Q_T \in \mathbb{R}^{n \times n}$ and $R \in \mathbb{R}^{m \times m}$ be symmetric, and fix an initial state $x_0 \in \mathbb{R}^n$. For a continuous control $u : [0, T] \to \mathbb{R}^m$, let $x_u$ be the solution of $\dot x = Ax + Bu$ on $[0, T]$ with $x_u(0) = x_0$, let

$$J(u) = \frac12 \int_0^T \big(x_u(t)^\top Q\, x_u(t) + u(t)^\top R\, u(t)\big)\, dt + \frac12 x_u(T)^\top Q_T\, x_u(T),$$

and let the adjoint $\lambda_u$ be the solution of $\dot\lambda = -A^\top \lambda - Q x_u$ on $[0, T]$ with $\lambda_u(T) = Q_T x_u(T)$. For continuous controls $u$ and $v$, let $\delta x = x_{u+v} - x_u$, the solution of $\dot{\delta x} = A\,\delta x + B v$ with $\delta x(0) = 0$, so that $\delta x(t) = \int_0^t e^{(t - s)A} B v(s)\, ds$.

1. **Exact increment.** For all continuous $u$ and $v$,

    $$J(u + v) - J(u) = \int_0^T \big(R u + B^\top \lambda_u\big)^\top v\, dt + \frac12 \Big[\int_0^T \big(\delta x^\top Q\, \delta x + v^\top R\, v\big)\, dt + \delta x(T)^\top Q_T\, \delta x(T)\Big].$$

2. **First variation.** $\frac{d}{d\varepsilon} J(u + \varepsilon v)\big|_{\varepsilon = 0} = \int_0^T (R u + B^\top \lambda_u)^\top v\, dt$.
3. **Necessity.** If $u$ minimizes $J$ over continuous controls, then $R u(t) + B^\top \lambda_u(t) = 0$ for every $t \in [0, T]$.
4. **Sufficiency and uniqueness.** If $Q$ and $Q_T$ are positive semidefinite, $R$ is positive definite and $R u(t) + B^\top \lambda_u(t) = 0$ for every $t \in [0, T]$, then $J(u) < J(w)$ for every continuous control $w \ne u$; so $u$ is the unique minimizer of $J$ over continuous controls.

**Proof.** The solutions $x_u$, $\lambda_u$ and $\delta x$ exist, are unique and are continuously differentiable on $[0, T]$ by variation of constants on a compact interval. Expanding the quadratic forms with $x_{u+v} = x_u + \delta x$ and using the symmetry of $Q$, $R$ and $Q_T$,

$$J(u + v) - J(u) = \int_0^T \big(x_u^\top Q\, \delta x + u^\top R\, v\big)\, dt + x_u(T)^\top Q_T\, \delta x(T) + \frac12\Big[\int_0^T \big(\delta x^\top Q\, \delta x + v^\top R\, v\big)\, dt + \delta x(T)^\top Q_T\, \delta x(T)\Big].$$

Next, $\frac{d}{dt}\big(\lambda_u^\top \delta x\big) = \dot\lambda_u^\top \delta x + \lambda_u^\top (A\,\delta x + B v) = -x_u^\top Q\, \delta x + \lambda_u^\top B v$. Integrating over $[0, T]$ and using $\delta x(0) = 0$ and $\lambda_u(T) = Q_T x_u(T)$ gives $x_u(T)^\top Q_T\, \delta x(T) = -\int_0^T x_u^\top Q\, \delta x\, dt + \int_0^T \lambda_u^\top B v\, dt$. Substituting, the terms in $x_u^\top Q\, \delta x$ cancel and the linear part becomes $\int_0^T (u^\top R + \lambda_u^\top B) v\, dt$, which is part 1. Replacing $v$ by $\varepsilon v$ multiplies $\delta x$ by $\varepsilon$, so the bracket is $\varepsilon^2$ times a constant, which gives part 2. For part 3, let $g = R u + B^\top \lambda_u$, a continuous function; minimality gives $J(u + \varepsilon g) - J(u) \ge 0$ for every real $\varepsilon$, so the derivative at $\varepsilon = 0$, $\int_0^T |g|^2\, dt$, is $0$, and a continuous function with $\int_0^T |g|^2 = 0$ vanishes on $[0, T]$. For part 4, take $v = w - u \ne 0$. The linear term is zero, the terms with $Q$ and $Q_T$ are nonnegative, and $v^\top R\, v \ge r |v|^2$ with $r > 0$ the smallest eigenvalue of $R$. A nonzero continuous $v$ is nonzero on a subinterval of positive length, so $\int_0^T |v|^2\, dt > 0$ and $J(w) - J(u) > 0$.

## Proof depends on

- [Variation of constants on a compact interval](../../ordinary-differential-equations/variation-of-constants-on-a-compact-interval.md): existence and uniqueness of $x_u$, $\delta x$ and $\lambda_u$ on $[0, T]$

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 9.2: Theorem 43 (p. 403), the necessary condition for optimal controls, in which the adjoint solves $\dot\lambda = -\nu_0 q_x^\top - A^\top\lambda$ with a final value given by the terminal cost and $\partial H/\partial u = 0$ almost everywhere, and Exercise 9.2.12 (p. 408), its specialization to $\dot x = Ax + Bu$ with costs $u^\top R u + x^\top Q x$ and $x^\top S x$, $Q, S \succeq 0$, $R \succ 0$. Sontag's costs carry no factor $\frac12$, so his adjoint is twice the one used here. The exact increment identity, the sufficiency and uniqueness argument and the restriction to continuous controls are derived on the page.
