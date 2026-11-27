# Bulk–surface Darcy flow model of Ezrin polarization

**Model.** A migrating cell (e.g. a zebrafish primordial germ cell) occupies a convex domain $\Omega \subset \mathbb R^n$ ($n = 3$ for the well-posedness theorem) with membrane $\Gamma = \partial\Omega$. Actin-generated forces $f$ (a measure compactly supported inside $\Omega$) drive an intracellular Darcy flow, and the membrane–cortex linker Ezrin, with surface density $u$ on $\Gamma$, is transported by the tangential flow, diffuses, and exchanges with the cytoplasm. In dimensionless form,

$$w = -\nabla p + f, \quad \operatorname{div}w = 0 \ \text{in } \Omega, \quad w\cdot n = 0 \ \text{on } \Gamma,$$

$$\partial_t u = -\operatorname{div}_\Gamma(u\,w) + \varepsilon\Delta_\Gamma u - d(w,u) + a(u,1) \ \text{on } \Gamma, \qquad u(0) = u_0,$$

where $a(u,1) = C_3u^{\alpha}(1-u)$ for $u \le 1$ (and $0$ for $u > 1$) is cooperative adsorption and $d(w,u) = (C_1|w| + C_2)u$ for $u \le 1$ is desorption enhanced by flow; for $u > 1$ the source uses $d(w,u) = (C_1|w| + C_2)\,\frac{u^\zeta + \zeta - 1}{\zeta}$ with an exponent $\zeta > 1$. Equivalently $\Delta p = \operatorname{div}f$ in $\Omega$ with $\nabla p\cdot n = f\cdot n$ on $\Gamma$.

**Theorem (flow regularity).** For convex $\Omega$ and $f$ compactly supported in $\Omega$, the pressure is $p = \tilde p + \int_\Omega \Psi(\cdot - z)\cdot df(z)$ with $\Psi(x) = x/(\omega_n|x|^n)$ and $\tilde p$ Lipschitz, and for every $s>n$

$$\|w\|_{L^\infty(\Gamma)} \le C(s,n,\Omega)\,\operatorname{dist}(\operatorname{spt}f,\Gamma)^{-s}\,\|f\|_{\mathcal M(\overline\Omega)};$$

on the unit ball in $\mathbb R^3$ the Neumann Green's function is explicit.

**Theorem (well-posedness).** Let $n = 3$, $\Gamma = \partial\Omega \subset \mathbb R^3$ be bounded and Lipschitz, $w \in L^\infty(\Gamma)$, and $q > 2$ with $q \ge \max\{\zeta, 2\zeta - 2\}$. For $u_0 \in L^q(\Gamma)$ the Ezrin equation has a unique weak solution, short-time in $C^0([0,\hat t];L^q) \cap C^0((0,\hat t];C^{0,\alpha})$ for $\alpha < 1-2/q$; for $u_0 > 0$ it stays non-negative with $\|u(t)\|_{L^q} \le \max\{\|u_0\|_{L^q}, M\}$, hence it extends to a unique global non-negative solution bounded uniformly in time.

**Proposition (Ezrin phases).** The local kinetics $\partial_t u = C_3u^\alpha(1-u) - (C_1|w| + C_2)u$ switch with the local flow speed $|w|$:

- $\alpha = 1$: transcritical bifurcation at $\bar w = (C_3 - C_2)/C_1$; for $|w| \ge \bar w$ only $u = 0$ (stable), for $|w| < \bar w$ the stable state is $u = (C_3 - C_2 - C_1|w|)/C_3$ and $0$ is unstable.
- $\alpha > 1$: saddle-node at $\bar w = \frac{C_3}{C_1}\frac{(1-1/\alpha)^{\alpha-1}}{\alpha} - \frac{C_2}{C_1}$; for $|w| < \bar w$ both $u = 0$ and a state in $\big[\frac{\alpha-1}{\alpha}, 1 - \frac{C_2}{C_3}\big]$ are stable (bistability).

Without transport the Ezrin equation is an Allen–Cahn-type $L^2$ gradient flow, so the membrane separates into an Ezrin-rich phase (where flow is slow, at the cell rear) and an Ezrin-free phase (where flow is fast), the latter marking the preferred bleb site.

## Expansion

Darcy flow driven by forces away from the boundary is smooth near $\Gamma$, which is why the $L^\infty$ bound degrades only through the distance of $\operatorname{spt}f$ to the membrane. The surface equation is a semilinear advection–diffusion–reaction problem treated as a perturbation of the Laplace–Beltrami heat semigroup on the Lipschitz surface (fixed-point argument), and the strong desorption above $u = 1$ gives the a priori $L^q$ bound needed for global existence. Coupling flow speed to desorption converts the spatial pattern of $|w|$ on $\Gamma$ into a stable polarized Ezrin distribution.

## Sources

- Carolin Dirks, Paul Striewski, Benedikt Wirth, Anne Aalto, Adan Olguin-Olguin and Erez Raz, "A mathematical model for cell polarization in zebrafish primordial germ cells", arXiv:1912.08627 (2019), Theorem 2 (existence and regularity of Darcy flow), Proposition 4 (Green's function on the ball), Theorem 7 (short-term existence), Proposition 9 (global boundedness), Corollary 10 (long-term existence), Proposition 11 (Ezrin phases), <https://doi.org/10.48550/arXiv.1912.08627>.
