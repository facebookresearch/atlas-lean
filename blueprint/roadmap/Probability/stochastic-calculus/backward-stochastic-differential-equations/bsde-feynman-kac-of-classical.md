# Nonlinear Feynman–Kac formula, classical case

Let $(\Omega, P)$ be a probability space, $B$ a real Brownian motion with continuous paths and $F$ its
[augmented filtration](is-augmented-brownian-filtration.md), and $T \ge 0$, $x \in \mathbb{R}$. Let
$b, \sigma, \varphi : \mathbb{R} \to \mathbb{R}$ be Lipschitz and $f : \mathbb{R}^3 \to \mathbb{R}$ with
$|f(x, y, z) - f(x', y', z')| \le \mu(|x - x'| + |y - y'| + |z - z'|)$. Let $X$ be an adapted process with
continuous paths, $\mathbb E \int_0^t X_s^2\, ds < \infty$ for every $t$, and, for every $t$, almost surely
$X_t = x + \int_0^t \sigma(X_s)\, dB_s + \int_0^t b(X_s)\, ds$ (the solution class of [strong solutions of
SDEs](../sde-lipschitz-exists-unique.md)). Let $u : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be $C^2$ with
$\partial_x u$ bounded and $|u(t, y)| \le C(1 + |y|)$, solving

$$\partial_t u + b\, \partial_x u + \tfrac12 \sigma^2\, \partial_x^2 u + f(y, u, \sigma\, \partial_x u) = 0 \quad \text{on } [0, T] \times \mathbb{R}, \qquad u(T, \cdot) = \varphi .$$

Then every [solution](is-bsdesolution.md) $(Y, Z)$ of the BSDE with generator
$(t, \omega, y, z) \mapsto f(X_t(\omega), y, z)$ and terminal value $\varphi(X_T)$ satisfies
$Y_t = u(t, X_t)$ almost surely for each $t \in [0, T]$; in particular $Y_0 = u(0, x)$. Peng states the
formula (Theorem 1.3) for the viscosity solution; the paragraph after it records his 1991 proof when the
PDE (1.11) has a classical solution.

## Informally uses

- [Existence and uniqueness for BSDEs with Lipschitz generators](bsde-exists-unique.md): Itô's
  formula shows that $(u(t, X_t), \sigma(X_t)\, \partial_x u(t, X_t))$ solves the BSDE, and uniqueness
  identifies it with $(Y, Z)$.

## Background

- [Itô's formula](../it-s-formula/README.md): the proof uses its version for $u(t, X_t)$ with $X$ an
  Itô process, of which the formula for $f(B_t)$ is the simplest case.
- [Strong solutions of SDEs with Lipschitz coefficients](../sde-lipschitz-exists-unique.md): the
  forward process $X$.

## Sources

- S. Peng, *Backward stochastic differential equation, nonlinear expectation and their applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I, Hindustan Book Agency, 2010, 393–432, Theorem 1.3 and the paragraph after it.
- S. Peng, *Probabilistic interpretation for systems of quasilinear parabolic partial differential equations*, Stochastics and Stochastic Reports 37 (1991), 61–74.
- E. Pardoux and S. Peng, *Backward stochastic differential equations and quasilinear parabolic partial differential equations*, in *Stochastic Partial Differential Equations and Their Applications*, Lecture Notes in Control and Information Sciences 176, Springer, 1992, 200–217.
