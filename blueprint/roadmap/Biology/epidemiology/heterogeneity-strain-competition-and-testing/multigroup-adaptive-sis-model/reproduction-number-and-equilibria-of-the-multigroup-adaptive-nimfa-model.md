# Reproduction number and equilibria of the multigroup adaptive NIMFA model

**Model.** Consider $n$ communities with normalized populations. Let $y_i \in [0,1]$ be the prevalence in community $i$ and $z_{ij} \in [0,1]$ the density of active links from community $j$ to community $i$. The multigroup adaptive N-intertwined mean-field approximation (aNIMFA) is

$$\begin{aligned} \dot y_i &= -\delta_i y_i + (1-y_i)\sum_{j=1}^n \beta_{ij}\,y_j\,z_{ij},\\ \dot z_{ij} &= -\zeta_{ij}\,z_{ij}\,f^{br}_{ij}(y_i,y_j,\bar y) + \xi_{ij}(1-z_{ij})\,f^{cr}_{ij}(y_i,y_j,\bar y), \qquad \bar y = \frac1n\sum_j y_j, \end{aligned}$$

with curing rates $\delta_i > 0$, infection rates $\beta_{ij} \ge 0$ forming an irreducible matrix, link-breaking and link-creation rates $\zeta_{ij}, \xi_{ij} > 0$, and awareness functions $f^{br}_{ij}$ (link breaking) and $f^{cr}_{ij}$ (link creation) that depend on local prevalences and the global mean prevalence.

**Disease-free equilibrium and $R_0$.** At $y = 0$ the link densities are $z_{ij}^{\mathrm{DFE}} = \dfrac{\xi_{ij}f^{cr}_{ij}(\mathbf{0})}{\zeta_{ij}f^{br}_{ij}(\mathbf{0}) + \xi_{ij}f^{cr}_{ij}(\mathbf{0})}$. The next-generation matrix and basic reproduction number are

$$F = \left(\frac{\beta_{ij}}{\delta_i}\,z^{\mathrm{DFE}}_{ij}\right)_{i,j=1}^n, \qquad R_0 = \rho(F).$$

- With fully homogeneous parameters, $R_0 = n\dfrac{\beta}{\delta}\dfrac{\xi f^{cr}(\mathbf{0})}{\zeta f^{br}(\mathbf{0}) + \xi f^{cr}(\mathbf{0})}$.
- If no links are broken at zero prevalence ($f^{br}_{ij}(\mathbf{0}) = 0$), then $z^{\mathrm{DFE}}_{ij} = 1$ and $R_0 = \rho\big((\beta_{ij}/\delta_i)\big)$, the reproduction number of NIMFA on the static network: adaptivity does not change the epidemic threshold.

**Theorem.**

1. If each $f^{br}_{ij}$ is non-decreasing and each $f^{cr}_{ij}$ non-increasing in all arguments, the DFE is globally stable when $R_0 < 1$.
2. The DFE is unstable when $R_0 > 1$.
3. If the minimum row sum or minimum column sum of $F$ exceeds $1$, the system has at least one endemic equilibrium.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Linearizing the prevalence equations at the DFE gives $J = M - V$ with $M_{ij} = \beta_{ij}z^{\mathrm{DFE}}_{ij}$ and $V = \operatorname{diag}(\delta_i)$, so the van den Driessche–Watmough next-generation method yields $R_0 = \rho(MV^{-1})$. For global stability, monotone awareness implies that link densities never exceed their disease-free values once prevalence is positive, so the prevalence dynamics are dominated by a cooperative linear system with spectral bound below zero when $R_0 < 1$. Existence of an endemic equilibrium uses a fixed-point argument on the feasible box, the row- or column-sum condition guaranteeing that the box away from $y = 0$ is mapped into itself. Numerically, asymmetric two-community networks can show sustained oscillations, unlike the single-community model.

## Sources

- Massimo A. Achterberg, Mattia Sensi and Sara Sottile, "A minimal model for multigroup adaptive SIS epidemics", Chaos: An Interdisciplinary Journal of Nonlinear Science 35 (2025), 033127, <https://doi.org/10.1063/5.0246228>; numbering as in arXiv:2407.17639: Section 2 (model), Section 3 (DFE, Equations for $R_0$ and $F$, Theorem 2, Corollary 4 and Theorem 5).
