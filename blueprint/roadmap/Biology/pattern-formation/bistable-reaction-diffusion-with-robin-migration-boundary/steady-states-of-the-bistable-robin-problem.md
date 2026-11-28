# Existence and stability of steady states of the bistable Robin problem

**Problem.** On $\Omega = (-L,L)$ consider

$$\partial_tp - \partial_{xx}p = f(p) \ \text{ in } (0,\infty)\times\Omega, \qquad \partial_\nu p = -D\,(p - p^{\mathrm{ext}}) \ \text{ on } \partial\Omega,$$

with initial data in $[0,1]$, migration rate $D > 0$ and exterior proportion $p^{\mathrm{ext}}\in(0,1)$, and its steady states $-p'' = f(p)$, $p'(\pm L) = \mp D(p(\pm L) - p^{\mathrm{ext}})$. Assume $f\in C^1([0,1])$ is **bistable**: $f(0) = f(\theta) = f(1) = 0$ for some $\theta\in(0,1)$, $f < 0$ on $(0,\theta)$, $f > 0$ on $(\theta,1)$, $\int_0^1 f > 0$; and $f'$ vanishes exactly at $\alpha_1\in(0,\theta)$ and $\alpha_2\in(\theta,1)$, with $f' < 0$ on $[0,\alpha_1)\cup(\alpha_2,1]$, $f' > 0$ on $(\alpha_1,\alpha_2)$, $f$ convex on $(0,\alpha_1)$ and concave on $(\alpha_2,1)$. Let $\beta\in(\theta,1)$ be the unique point with $\int_0^\beta f = 0$. A steady state is **(SD)** (resp. **(SI)**) if it is even, decreasing (resp. increasing) on $(0,L)$.

**Theorem.**

1. (Symmetric steady states.) There are thresholds $M_d, M_i : (0,1)\times(0,\infty)\to[0,\infty]$ such that an (SD) solution exists iff $L\ge M_d(p^{\mathrm{ext}},D)$, with values in $[p^{\mathrm{ext}},1]$, and an (SI) solution exists iff $L\ge M_i(p^{\mathrm{ext}},D)$, with values in $[0,p^{\mathrm{ext}}]$. Moreover:
   - if $p^{\mathrm{ext}} < \theta$: $M_i = 0$ and $0 < M_d < \infty$; the (SI) solution is unique when $p^{\mathrm{ext}}\le\alpha_1$;
   - if $\theta < p^{\mathrm{ext}} < 1$: $M_d = 0$, and the (SD) solution is unique when $p^{\mathrm{ext}}\ge\alpha_2$; if $p^{\mathrm{ext}}\le\beta$ then $0 < M_i < \infty$ for all $D$, while if $p^{\mathrm{ext}} > \beta$ there is $D_\ast > 0$ with $M_i < \infty$ for $D < D_\ast$ and $M_i = \infty$ for $D\ge D_\ast$;
   - if $p^{\mathrm{ext}} = \theta$: $M_d = M_i = 0$ and $p\equiv\theta$ is a steady state.
2. (Non-symmetric-monotone steady states.) There is $M_\ast$ such that a steady state that is neither (SD) nor (SI) exists iff $L\ge M_\ast(p^{\mathrm{ext}},D)$; if $p^{\mathrm{ext}}\le\beta$ then $0 < M_i + M_d < M_\ast < \infty$, and if $p^{\mathrm{ext}} > \beta$ then $0 < M_i < M_\ast < \infty$ for $D < D_\ast$ and $M_\ast = \infty$ for $D\ge D_\ast$. No steady state is monotone on all of $(-L,L)$ unless $p^{\mathrm{ext}} = \theta$.
3. (Linearized stability.) Let $\lambda_1\in(0,\pi^2/(4L^2))$ be the smallest positive root of $\sqrt\lambda\,\tan(L\sqrt\lambda) = D$. A steady state $p$ is asymptotically stable if $f'(p(x)) < \lambda_1$ on $(-L,L)$ and unstable if $f'(p(x)) > \lambda_1$ on $(-L,L)$; in particular steady states with values in $[0,\alpha_1]$ or $[\alpha_2,1]$ are asymptotically stable.
4. (Small zones.) If $p^{\mathrm{ext}}\le\alpha_1$, for every $L$ there is exactly one (SI) steady state and it is asymptotically stable; it is the only steady state when $L < M_d$. Symmetrically, if $p^{\mathrm{ext}}\ge\alpha_2$ there is exactly one (SD) steady state, asymptotically stable, and the only one when $L < M_i$.

Biologically, with $p$ the *Wolbachia* proportion, a small treated zone surrounded by a mostly wild exterior ($p^{\mathrm{ext}}\le\alpha_1$) is driven to the low-proportion state: migration defeats replacement unless the zone exceeds $M_d$.

## Expansion

Steady states are orbits of the Hamiltonian system $p' = q$, $q' = -f(p)$ with energy $\tfrac12q^2 + F(p)$, $F = \int_0^pf$; the Robin conditions require the orbit to start and end on the lines $q = \mp D(p - p^{\mathrm{ext}})$. The time needed to travel along an energy level between these lines (a time map) gives the half-length $L$, and its range as the energy varies defines $M_d$, $M_i$, $M_\ast$ (the level $F(\beta) = F(0)$ separates the qualitatively different orbit families). Stability follows from the principle of linearized stability: the principal Robin eigenvalue of $-\partial_{xx}$ on $(-L,L)$ is $\lambda_1$, so the sign of $f'(p) - \lambda_1$ controls the principal eigenvalue of the linearization.

## Sources

- Luís Almeida, Pierre-Alexandre Bliman, Nga Nguyen, Nicolas Vauchelet, "Steady-state solutions for a reaction-diffusion equation with Robin boundary conditions: application to the control of dengue vectors", arXiv (2022). Section 2 (Assumptions 2.1–2.2, Theorems 2.1–2.3, Corollary 2.1), Section 4 (application to *Wolbachia*). <https://doi.org/10.48550/arXiv.2209.07165>. Published version: European Journal of Applied Mathematics 35(3) (2024), 382–408, <https://doi.org/10.1017/s0956792523000256>; locators above refer to the arXiv version.
