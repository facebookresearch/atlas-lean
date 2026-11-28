# Continuum limits of the on-lattice agent-based model of oncolytic virus infection

On the lattice $x_j = j\delta$, $j \in \mathbb{Z}$, with time steps $t_n = n\tau$, let $u_j^n$ and $i_j^n$ be the densities of uninfected and infected tumour cells and $\rho_j^n = u_j^n + i_j^n$ the pressure (taken equal to the total density). With a smooth decreasing $G$ vanishing at the homeostatic pressure $\bar P$, in each step an uninfected cell divides with probability $\tau G(\rho_j^n)_+$ and dies with probability $\tau G(\rho_j^n)_-$; it becomes infected with probability $\tau \beta i_j^n / K$; an infected cell lyses with probability $\tau q$. Cells move to $x_{j \pm 1}$ either

- by an unbiased random walk, with probabilities $\theta_u/2$ (uninfected) and $\theta_i/2$ (infected), or
- down the pressure gradient, with probabilities $\theta_k (\rho_j^n - \rho_{j\pm1}^n)_+ / (2\bar P)$, $k \in \{u, i\}$,

where $\theta_u, \theta_i \in [0, 1]$.

**Formal limit.** Let $\tau, \delta \to 0$ with $\delta^2/(2\tau) \to D$, and set $D_u = \theta_u D$, $D_i = \theta_i D$. Take logistic growth $G(\rho) = p(1 - \rho/\bar P)$, so that the carrying capacity is $K = \bar P$. Undirected movement gives the reaction-diffusion system

$$\partial_t u = D_u \partial_{xx} u + p u \Big(1 - \frac{u + i}{K}\Big) - \frac{\beta}{K} u i, \qquad \partial_t i = D_i \partial_{xx} i + \frac{\beta}{K} u i - q i,$$

and pressure-driven movement gives the local cross-diffusion system

$$\partial_t u = \frac{D_u}{K} \partial_x\big[u\, \partial_x (u + i)\big] + p u \Big(1 - \frac{u + i}{K}\Big) - \frac{\beta}{K} u i, \qquad \partial_t i = \frac{D_i}{K} \partial_x\big[i\, \partial_x (u + i)\big] + \frac{\beta}{K} u i - q i.$$

In two dimensions the four-neighbour walk with probabilities $\theta_k/4$ (or $\theta_k(\rho_j - \rho_{j+e})_+/(4\bar P)$) needs the scaling $\delta^2/(4\tau) \to D$.

## Expansion

Write the expected density at $x_j$ after one step as gains from neighbours minus losses, Taylor-expand $u(t + \tau, x)$ and $u(t, x \pm \delta)$ about $(t, x)$, divide by $\tau$ and pass to the limit. For the unbiased walk the second differences produce $D_u \partial_{xx} u$. For the pressure-driven walk the positive parts $(\rho_j - \rho_{j\pm1})_+$ combine to a discrete divergence of $u\,\partial_x \rho$, giving a porous-medium-type flux. Infected cells play the role of predators that also count toward the saturation of uninfected growth, which separates this system from the diffusive Lotka-Volterra model studied by Dunbar. The derivation is formal; no convergence theorem is proved. Front speeds of the limiting equations, such as the [Fisher–KPP minimal speed](../../../../pattern-formation/fisher-kpp-travelling-waves/two-mul-sqrt-le-of-is-front.md), are studied on the companion page and are not used in this derivation.

## Sources

- D. Morselli, M. E. Delitala and F. Frascoli, Agent-based and continuum models for spatial dynamics of infection by oncolytic viruses, *Bull. Math. Biol.* 85 (2023), article 92, <https://doi.org/10.1007/s11538-023-01192-x>, PMCID PMC10471645. Section 2, equations (1)-(7), Remarks 1-2, Appendix A.
