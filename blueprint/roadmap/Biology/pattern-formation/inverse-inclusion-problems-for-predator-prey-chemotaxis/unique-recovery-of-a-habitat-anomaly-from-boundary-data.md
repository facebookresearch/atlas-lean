# Unique recovery of a habitat anomaly from boundary data in cross-diffusion predator-prey chemotaxis

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded domain with $C^2$ boundary, $Q = \Omega \times (0, T]$. Chemical concentrations $\mathbf{u} = (u_1, \dots, u_N)$ and prey densities $\mathbf{v} = (v_1, \dots, v_M)$ solve the cross-diffusion chemotaxis system

$$
\begin{aligned}
\partial_t u_i - d_i \Delta\Big(u_i + \sum_{j=1}^M \delta_{ij} u_i v_j\Big) &= G_i(x, t, \mathbf{u}, \mathbf{v}), & i = 1, \dots, N,\\
\partial_t v_j - \delta_j \Delta v_j &= \sum_{i=1}^N \chi^i_j \nabla \cdot (v_j \nabla u_i), & j = 1, \dots, M,
\end{aligned}
$$

in $Q$, with $d_i, \delta_j, \delta_{ij} > 0$ and $\chi^i_j \in \{0, 1\}$, together with initial data $\mathbf{u}(\cdot, 0) = \mathbf{f}$, $\mathbf{v}(\cdot, 0) = \mathbf{g}$. The stationary version replaces $\partial_t$ by $0$ and $G$ by a time-independent reaction $F$, with Dirichlet data $(\mathbf{f}, \mathbf{g})$ on $\partial\Omega$.

**Anomaly.** A habitat anomaly is an open subdomain $\omega \Subset \Omega$ with $\Omega \setminus \omega$ connected, across which the reaction law jumps:

$$
\mathbf{G} = \mathbf{G}^0 + (\mathbf{G}^1 - \mathbf{G}^0)\,\chi_\omega ,
$$

where $\mathbf{G}^1$ and $\mathbf{G}^0$ are admissible on $\omega$ and $\Omega \setminus \omega$ respectively (holomorphic in $(\mathbf{u}, \mathbf{v})$ with values in $C^{2+\alpha, 1+\alpha/2}$, Hölder in $(x,t)$, vanishing at a fixed non-negative constant steady state $(\mathbf{u}_0, \mathbf{0})$), and $\mathbf{G}^0 \not\equiv \mathbf{G}^1$ on $\partial\omega \times (0, T)$. In the stationary case the analogous condition is that for some $\ell$ the $\ell$-th Taylor coefficients of $F^1$ and $F^0$ are Hölder continuous and differ on each side of $\partial \omega$ near $\partial\omega$.

**Theorem (smooth anomalies, time-dependent).** If $\partial\omega \in C^2$ and $\mathbf{G}$ is admissible, then the measurement map of non-negative solutions

$$
\mathcal{M}^+_{\omega, \mathbf{G}} : (\mathbf{f}, \mathbf{g}) \mapsto \big((\mathbf{u}, \mathbf{v})|_{\partial\Omega},\ (\mathbf{u}, \mathbf{v})|_{t = T}\big)
$$

uniquely determines $\omega$ and the boundary values $\mathbf{G}(x, t, \mathbf{u}, \mathbf{v})|_{\partial\omega}$: if $\mathcal{M}^+_{\omega_1, \mathbf{G}_1} = \mathcal{M}^+_{\omega_2, \mathbf{G}_2}$ then $\omega_1 = \omega_2$ and the jumps agree on $\partial\omega_1$.

**Theorem (polyhedral anomalies, stationary).** If $\omega$ is a convex polyhedron (or, by corollary, a convex domain with conic corners, or a $C^2$ domain) and $\mathbf{F}$ is admissible, then the stationary boundary measurement $\mathcal{M}^+_{\omega, \mathbf{F}}$ (normal fluxes $(\partial_\nu \mathbf{u}, \partial_\nu \mathbf{v})|_{\partial\Omega}$ for prescribed Dirichlet data) uniquely determines both $\omega$ and $\mathbf{F}$.

## Expansion

The proof uses successive linearization around the constant steady state $(\mathbf{u}_0, \mathbf{0})$: inputs $\mathbf{f} = \mathbf{u}_0 + \sum_k \varepsilon_k \mathbf{f}_k$ give solutions holomorphic in $\varepsilon$, and the $\ell$-th order derivatives in $\varepsilon$ solve linear parabolic or elliptic equations whose sources are the $\ell$-th Taylor coefficients of the reaction. The positivity constraint is kept by perturbing around a non-negative state. If two anomalies differ, one finds a boundary point of $\omega_1$ outside $\omega_2$ (smooth case) or a vertex of a polyhedron (corner case). In the smooth case, comparing the two linearized solutions across $\partial \omega_1$ gives a contradiction with the jump condition. In the corner case, complex geometric optics solutions $w = e^{\tau(\xi + i\xi^\perp)\cdot(x - x_c)}$ of the Laplace equation, which decay exponentially away from the vertex, are tested against the difference equation; the integral over the corner sector is bounded below by a power of $\tau$, while all other terms decay, forcing the Taylor coefficients to agree at the vertex. Biologically, $\omega$ is a degraded zone where predation, mortality or chemotactic rules change discontinuously, and the theorem says such zones are visible from boundary population data alone.

## Sources

- Yuhan Li, Hongyu Liu and Catharine W. K. Lo, "Determining habitat anomalies in cross-diffusion predator-prey chemotaxis models", arXiv (2025), governing and stationary systems of Section 1.2 ("Mathematical setup"), Definition 2.2, Theorem 2.4, Definition 3.3, Theorem 3.4, Corollaries 3.5 and 3.6, Lemma 3.1, <https://doi.org/10.48550/arXiv.2512.22946>.
