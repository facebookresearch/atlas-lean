# Finite-time blow-up in the chemotaxis–May–Nowak system below the diffusion threshold

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded smooth domain. Uninfected cells $u$, infected cells $v$ and free virus $w$ follow the quasilinear chemotaxis–May–Nowak system
$$
\begin{cases}
u_t = \nabla\cdot\big((1+u)^{m-1}\nabla u\big) - \chi\nabla\cdot(u\nabla v) - u - uw + \varphi, \\
\tau v_t = \Delta v - v + uw, \\
w_t = \Delta w - w + v,
\end{cases}
\qquad x \in \Omega,\ t > 0,
$$
with homogeneous Neumann conditions, $\chi > 0$, $m > 0$, and $\tau \in \{0,1\}$ ($\tau = 0$: parabolic–elliptic–parabolic; $\tau = 1$: fully parabolic). Uninfected cells are attracted to infected ones, infection $uw$ converts $u$ into $v$, and $\varphi \in C^\alpha(\overline\Omega\times[0,\infty))$ with $0 \le \varphi \le \varphi_*$ is the cell supply. Initial data $u_0, w_0 \in W^{2,\infty}(\Omega)$ are nonnegative, not identically zero, with zero normal derivative (and likewise $v_0$ when $\tau = 1$).

**Theorem.** Take $\tau = 0$, $\Omega = B_R(0)$ and $\varphi$ radial in space.
1. ($n = 3$.) If $1 < m \le 4/3$, then for every $\mu > 0$ there are nonnegative radial data $(u_0,w_0)$ with $\int_\Omega u_0 = \mu$ whose solution blows up in finite time: $T_{\max} < \infty$ and $\limsup_{t\nearrow T_{\max}}\|u(\cdot,t)\|_{L^\infty(\Omega)} = \infty$. One may take $w_0 \equiv W_0$ with any constant $W_0 > 0$ when $1 < m < 4/3$, and any sufficiently large $W_0$ when $m = 4/3$.
2. ($n \ge 4$.) If $0 < m \le 2 - 2/n$, the same holds for every $\mu > 0$, with $w_0 \equiv W$ for any $W > 0$ if $m < 2 - 2/n$ and sufficiently large $W$ if $m = 2 - 2/n$.

Blow-up thus occurs for arbitrarily small cell mass, unlike the mass-threshold phenomenon of the classical two-dimensional Keller–Segel system.

## Expansion

With $\tau = 0$ the infected-cell equation $-\Delta v + v = uw$ is elliptic, and a spatially constant initial virus load keeps $w$ bounded below on a time interval, so $uw$ acts like a Keller–Segel source proportional to $u$. In radial coordinates the cumulated mass $U(s,t) = \int_0^{s^{1/n}} \rho^{n-1}u\,d\rho$ satisfies a scalar degenerate parabolic inequality. A weighted moment of $U$ (a linear moment for $0 < m \le 1$, a logarithmic moment for $1 < m \le 2 - 2/n$, adapting the Tao–Winkler argument for linear diffusion) obeys a superlinear differential inequality whenever the diffusion exponent is at most the critical value, so data concentrated near the origin collapse in finite time.

## Sources

- Xueli Bai, Fang Li and Suying Liu, "Global Boundedness and Finite-Time Blow-up for a Quasilinear Chemotaxis--May--Nowak System", arXiv:2610.33664 (2026), Section 1, Theorems 1.2 and 1.3; Sections 4 and 5 (radial moment arguments), <https://doi.org/10.48550/arXiv.2610.33664>.
