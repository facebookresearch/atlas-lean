# Poisson network SIR as a reparametrized classical SIR model

**Setting.** An SIR epidemic spreads on a configuration-model random graph on $n$ nodes with Poisson degree distribution of mean $\mu$, per-edge transmission rate $\beta$ and recovery rate $\gamma$. Since the Poisson law has excess mean degree $\mu_{ex} = \mu$ ($\kappa = \mu_{ex}/\mu = 1$), the pairwise closure $[ASI] \approx \kappa[AS][SI]/[S]$ is exact as $n \to \infty$, and the limiting proportions with $S(0) = 1$, $I(0) = \rho$ satisfy

$$\dot S = -\tilde\beta\,S\big(1 + \rho - S + \tilde{\mathcal R}^{-1}\log S\big), \qquad \dot I = -\dot S - \gamma I, \qquad R = 1 + \rho - S - I,$$

with $\tilde\beta = \mu\beta$, $\tilde\gamma = \beta + \gamma$ and the network reproduction number $\tilde{\mathcal R} = \tilde\beta/\tilde\gamma = \mu\beta/(\beta + \gamma)$.

The classical SIR model with initial infected fraction $d$, infection rate $b$ and recovery rate $c$ has the same structure,

$$\dot S = -b\,S\big(1 + d - S + \mathcal{R}_0^{-1}\log S\big), \qquad \dot I = -\dot S - cI, \qquad \mathcal{R}_0 = b/c .$$

**Proposition.** The epidemic-curve equations (hence the $S$-curves) of the Poisson network model and of the classical SIR model coincide iff $b = \tilde\beta$, $d = \rho$ and $c = \tilde\gamma$; then $\mathcal R_0 = \tilde{\mathcal R}$. In that case, if $\mathcal R_0 < \mu$, the network model's infection curve satisfies

$$\dot I = -\dot S - c\Big(1 - \frac{\mathcal R_0}{\mu}\Big)I,$$

so the two models differ only through the recovery term, by the factor $1 - \mathcal R_0/\mu$, which tends to $1$ as the mean degree grows: the classical SIR model is the dense-network limit, and the mean degree $\mu$ is one extra parameter capturing contact heterogeneity.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

In the classical model $\dot I = -\dot S - cI$ and $\dot S = -bSI$; integrating $\dot S/S = -b I$ and eliminating $I$ with the conservation law yields the closed $S$ equation with the $\log S$ term. For the Poisson network the exact pairwise closure leads to the same closed form with $(\tilde\beta, \tilde\gamma, \rho)$, where the effective "recovery" $\tilde\gamma = \beta + \gamma$ in the $S$ equation includes edges lost when a partner transmits. The infected compartment however still recovers at rate $\gamma = \tilde\gamma - \tilde\beta/\mu = c(1 - \mathcal R_0/\mu)$, which gives the corrected infection curve. Matching coefficients of the two closed $S$ equations proves the "iff".

## Sources

- J. K. Wairimu, A. Gothard and G. A. Rempała, "Poisson Network SIR Epidemic Model", *Afrika Matematika* 36(3) (2025), 119, Theorem 1 and Proposition 1, <https://doi.org/10.1007/s13370-025-01339-0> (preprint arXiv:2501.00187).
