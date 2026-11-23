# Existence and uniqueness for BSDEs with Lipschitz generators

Let $(\Omega, P)$ be a probability space, $B$ a real Brownian motion with continuous paths and $F$ its
[augmented filtration](is-augmented-brownian-filtration.md), and $T \ge 0$. Let the generator
$g(t, \omega, y, z)$ be such that for each $(y, z)$ the process $(t, \omega) \mapsto g(t, \omega, y, z)$
is progressive with $\mathbb E \int_0^T g(t, y, z)^2\, dt < \infty$, and Lipschitz in $(y, z)$:
$|g(t, \omega, y, z) - g(t, \omega, y', z')| \le \mu(|y - y'| + |z - z'|)$. Then for every $F_T$-measurable
square-integrable $\xi$:

1. the BSDE $Y_t = \xi + \int_t^T g(s, Y_s, Z_s)\, ds - \int_t^T Z_s\, dB_s$ has a
   [solution](is-bsdesolution.md) $(Y, Z)$ in $M^2(0, T)$ whose $Y$ has almost surely continuous paths
   on $[0, T]$;
2. any two solutions $(Y, Z)$, $(Y', Z')$ agree in $M^2(0, T)$:
   $\mathbb E \int_0^T \bigl(|Y_s - Y'_s|^2 + |Z_s - Z'_s|^2\bigr)\, ds = 0$.

This is the case $d = m = 1$ of Peng's Theorem 1.1, due to Pardoux and Peng.

## Background

- [Itô isometry for progressive integrands](../it-integral/lintegral-ito-integral-sq-of-is-progress.md):
  the $L^2$ theory of the integral $\int Z\, dB$ in which the equation and the space $M^2(0, T)$ are set;
  a general nonlinear BSDE "can be still solved by a fixed point approach" (S. Peng, *BSDE, PDE,
  Nonlinear Expectation and Model Uncertainty*, IMS–NUS lecture notes, abstract).
- [Strong solutions of SDEs with Lipschitz coefficients](../sde-lipschitz-exists-unique.md): the
  forward analogue; there the initial value is prescribed, here the terminal value, and the
  martingale representation theorem supplies the unknown $Z$.

## Sources

- S. Peng, *Backward stochastic differential equation, nonlinear expectation and their applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I, Hindustan Book Agency, 2010, 393–432, Theorem 1.1.
- E. Pardoux and S. Peng, *Adapted solution of a backward stochastic differential equation*, Systems & Control Letters 14 (1990), 55–61.
