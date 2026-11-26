# Comparison theorem for one-dimensional BSDEs

Let $(\Omega, P)$ be a probability space, $B$ a real Brownian motion with continuous paths and $F$ its
[augmented filtration](is-augmented-brownian-filtration.md), and $T \ge 0$. Let
$g_1, g_2 : [0, \infty) \times \Omega \times \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be generators such
that for each $(y, z)$ the process $(t, \omega) \mapsto g_i(t, \omega, y, z)$ is progressive with
$\mathbb E \int_0^T g_i(t, y, z)^2\, dt < \infty$, and that are Lipschitz in $(y, z)$ with a common constant
$\mu$: $|g_i(t, \omega, y, z) - g_i(t, \omega, y', z')| \le \mu(|y - y'| + |z - z'|)$. Let $\xi_1, \xi_2$ be
$F_T$-measurable and square integrable, with $\xi_1 \ge \xi_2$ almost surely, and suppose that for all
$(t, y, z)$, $g_1(t, y, z) \ge g_2(t, y, z)$ almost surely. If $(Y^1, Z^1)$ and $(Y^2, Z^2)$ are
[solutions](is-bsdesolution.md) of the BSDEs with data $(g_1, \xi_1)$ and $(g_2, \xi_2)$, then for every
$t \in [0, T]$, $Y^1_t \ge Y^2_t$ almost surely.

## Background

- [Existence and uniqueness for BSDEs with Lipschitz generators](bsde-exists-unique.md): the
  solutions compared here exist and are unique. The comparison theorem is the "maximum principle"
  of one-dimensional BSDEs (Peng, Section 1.2) and makes the g-expectation $\xi \mapsto Y_0$
  monotone.

## Sources

- S. Peng, *Backward stochastic differential equation, nonlinear expectation and their applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I, Hindustan Book Agency, 2010, 393–432, Theorem 1.2.
- S. Peng, *A generalized dynamic programming principle and Hamilton–Jacobi–Bellman equation*, Stochastics and Stochastic Reports 38 (1992), 119–134.
- N. El Karoui, S. Peng and M.-C. Quenez, *Backward stochastic differential equations in finance*, Mathematical Finance 7 (1997), 1–71.
