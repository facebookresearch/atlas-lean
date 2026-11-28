# Persistence of arbitrarily many phytoplankton species under light-spectrum partitioning

**Model.** In a water column $0 < x < L$, $N$ phytoplankton species with densities $u_i$ obey

$$\partial_t u_i = D_i\,\partial_x^2 u_i - \alpha_i\,\partial_x u_i + \big[g_i(\gamma_i(x,t)) - d_i(x)\big]u_i,\qquad D_i\partial_x u_i - \alpha_i u_i = 0 \text{ at } x = 0, L,$$

for $1 \le i \le N$, with $D_i > 0$, $\alpha_i \in \mathbb{R}$, increasing saturating growth functions $g_i$ ($g_i(0) = 0$, $g_i' > 0$, $g_i(\infty) < \infty$), absorbed photon flux

$$\gamma_i(x,t) = \int_{400}^{700}k_i(\lambda)\,I(\lambda,x,t)\,d\lambda,\qquad I(\lambda,x,t) = I_{\rm in}(\lambda)\exp\Big[-K_{BG}(\lambda)x - \sum_{j=1}^N k_j(\lambda)\int_0^x u_j(y,t)\,dy\Big],$$

absorption spectra $k_i$, incident spectrum $I_{\rm in}$ and background attenuation $K_{BG}$.

**Theorem.** Suppose $I_{\rm in}(\lambda) > 0$ on an open subset of $[400, 700]$. Then for every $N \ge 1$ there exist death rates $d_i$ and absorption spectra $k_1,\dots,k_N$ such that all $N$ species persist: for every positive initial condition,

$$\liminf_{t\to\infty}\ \inf_{0 \le x \le L} u_i(x,t) > 0\qquad\text{for each } 1 \le i \le N.$$

The number of coexisting species supported by a single continuous resource, light, is therefore unbounded, in contrast to the one-species-per-resource count of Gause's competitive exclusion principle.

## Depends on

- [Coexistence and exclusion of phytoplankton competing for the light spectrum](coexistence-and-exclusion-of-phytoplankton-competing-for-the-light-spectrum.md)

## Expansion

Choose an interval $[\lambda_1, \lambda_2]$ on which $I_{\rm in}$ is bounded below, split it into $N$ subintervals $J_i$, and let $k_i$ be supported in the interior of $J_i$. On the support of $k_i$ only species $i$ attenuates light, so $\gamma_i$ depends on $u_i$ alone and each species solves a decoupled single-species water-column equation. Taking each $d_i$ to be a small positive constant makes the principal eigenvalue of the linearization at zero negative, so each decoupled equation has a unique positive steady state that attracts all positive solutions, giving uniform persistence of every species. Disjoint spectral niches thus turn one competition problem into $N$ independent persistence problems.

## Sources

- Christopher M. Heggerud, King-Yeung Lam and Hao Wang, "Niche differentiation in the light spectrum promotes coexistence of phytoplankton species: a spatial modelling approach", Journal of Mathematical Biology 86 (2023), 54, <https://doi.org/10.1007/s00285-023-01890-z>; numbering as in arXiv:2109.02634: Theorem 6.1.
