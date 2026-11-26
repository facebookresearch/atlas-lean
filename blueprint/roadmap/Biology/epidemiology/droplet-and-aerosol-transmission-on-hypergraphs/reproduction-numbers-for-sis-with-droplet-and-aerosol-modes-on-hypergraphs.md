# Reproduction numbers for SIS with droplet and aerosol modes on hypergraphs

**Model.** On a hypergraph with $N$ nodes, dyadic edges $E_d$ and environmental hyperedges $E_e$ of size $s \ge 3$, node $i$ is infected with probability $x_i$ and hyperedge $\ell$ is contaminated with probability $y_\ell$. With incidence indicators $\mathbb I_{ih}$, the mean-field dynamics are

$$\dot x_i = \Bigl(\beta_d \sum_{h \in E_d}\mathbb I_{ih}\sum_{j \ne i} x_j \mathbb I_{jh} + \beta_e \sum_{h \in E_e} \mathbb I_{ih} y_h\Bigr)(1 - x_i) - \gamma x_i, \qquad \dot y_\ell = \sigma\, g\Bigl(\sum_j x_j \mathbb I_{j\ell}\Bigr)(1 - y_\ell) - \delta y_\ell,$$

with droplet rate $\beta_d$, aerosol infection rate $\beta_e$, recovery $\gamma$, contamination rate $\sigma$ through an increasing function $g$ with $g(0) = 0$, and decontamination rate $\delta$.

**Theorem.**
1. *(Complete uniform hypergraph.)* The disease-free equilibrium is locally asymptotically stable if $R_0^{c} < 1$ and unstable if $R_0^{c} > 1$, where

$$R_0^{c} = \frac{\beta_d (N - 1)}{\gamma} + \frac{\beta_e\, \sigma\, g'(0)\binom{N-1}{s-1} s}{\gamma\,\delta}.$$

2. *(Regular uniform hypergraph.)* For each node in $k_d$ edges and $k_e$ hyperedges of size $s$, the mean-field model has

$$R_0^{ru} = \frac{\beta_d k_d}{\gamma} + \frac{\beta_e\,\sigma\, g'(0)\, k_e\, s}{\gamma\,\delta} = \frac{2\beta_d M_d}{N\gamma} + \frac{\beta_e\, \sigma\, g'(0)\, M_e\, s^2}{N\gamma\delta},$$

with $M_d, M_e$ the numbers of edges and hyperedges. If $R_0^{ru} < 1$ the disease-free equilibrium is locally asymptotically stable; if $R_0^{ru} > 1$ it is unstable and there is a unique, locally asymptotically stable endemic equilibrium.

## Expansion

Each reproduction number adds a droplet term (direct contacts times infection probability per infectious period) and an aerosol term: an infected node contaminates each of its environments at rate $\sigma g'(0)$, which stays contaminated for mean time $1/\delta$ and exposes its $s$ members. Linearising at the disease-free state gives a nonnegative next-generation structure whose spectral radius is explicit by symmetry of complete and regular hypergraphs. Writing $R_0^{ru}$ with a fixed number of hyperedges shows the aerosol term grows like $s^2$, so reducing group size is an effective control; heavy-tailed hyperedge-size distributions prolong disease persistence.

## Sources

- T. D. Nguyen, M. A. Porter, "A disease-spread model on hypergraphs with distinct droplet and aerosol transmission modes", arXiv:2601.03563 (2026), Theorems 3.1, 3.3 and 3.6, <https://doi.org/10.48550/arXiv.2601.03563>.
