# Strong-migration reductions and spatial limits

When migration is strong compared with drift, a structured population drifts like a single panmictic population. Felsenstein (Section VII.5) shows for the $n$-island model that the population drifts as one panmictic population of size near $Nn$ when $Nm$ is large and that structure impedes the spread of alleles when $Nm$ is small, with the transition near $4Nm = (n - 1)/n$, and reports that Nagylaki (1977) proved that any connected geographic structure behaves as if panmictic when all the $Nm_{ij}$ are large. With genic selection in Wright's island model, Cherry and Wakeley (2003, abstract) relate the subdivided population to a panmictic Wright–Fisher population with a larger effective size and a smaller effective selection coefficient whose product is unchanged.

In the structured diffusion with migration rates multiplied by a large factor $\lambda$, the deme frequencies are pulled towards their weighted average, and the candidate one-dimensional limit for $\bar x = \sum_iw_ix_i$, with $w$ the stationary law of the backward migration chain, has drift $\sum_iw_i\beta_i(\bar x)$ and diffusion coefficient $\sum_iw_i^2\bar x(1 - \bar x)/\kappa_i$, obtained by evaluating the drift and the quadratic-variation rate of $\bar x$ at the equal-frequency configuration.

For populations in a spatial continuum the limits are stochastic partial differential equations, not the deterministic Fisher–KPP equation. Biswas, Etheridge and Klimek (arXiv 2018, Section 1, equations (1.1), (1.2)) obtain, for selection fluctuating between two environments, the one-dimensional equation $dw = \frac12\Delta w\,dt + s^2w(1 - w)(1 - 2w)\,dt + \sqrt{w(1 - w)}\,W(dt, dx) + \sqrt2\,sw(1 - w)\,\tilde W(dt, dx)$ with space-time white noise $W$ for genetic drift and an independent noise $\tilde W$, white in time but possibly coloured in space, for the environmental fluctuations. In the scaling limit of the spatial Lambda–Fleming–Viot process in dimension at least two (their Theorem 4.6, equations (4.4)–(4.5)), only the genetic-drift term $\sqrt{w(1 - w)}\,W(dt, dx)$ disappears: the limit keeps the Laplacian, the deterministic cubic term $s^2w(1 - w)(1 - 2w)$ and the environmental noise term, now driven by spatially coloured noise.

## Expansion

1. The structured diffusion with migration rates scaled by $\lambda$.
2. Convergence of $\bar x$ as $\lambda \to \infty$ to the one-dimensional diffusion with averaged coefficients, and the collapse of the differences between demes.
3. The effective size and selection coefficient of the island model in this limit.
4. Continuum limits: the one-dimensional stochastic equation with genetic-drift and environmental noise, and the higher-dimensional limit in which only the genetic-drift noise disappears. Removing both noise terms leaves the reaction–diffusion equation with the sign-changing cubic reaction $s^2w(1 - w)(1 - 2w)$, not the logistic Fisher–KPP equation; any comparison with Fisher–KPP travelling waves is a separate statement.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, course text, University of Washington, Section VII.5 (the island model; discussion around equations (VII-49)–(VII-51)).
- J. L. Cherry and J. Wakeley, A diffusion approximation for selection and drift in a subdivided population, Genetics 163 (2003), 421–428, abstract. <https://doi.org/10.1093/genetics/163.1.421>
- N. Biswas, A. M. Etheridge and A. Klimek, The spatial Lambda-Fleming-Viot process with fluctuating selection, arXiv:1802.08188, Section 1 and Theorem 4.6. <https://arxiv.org/abs/1802.08188>
