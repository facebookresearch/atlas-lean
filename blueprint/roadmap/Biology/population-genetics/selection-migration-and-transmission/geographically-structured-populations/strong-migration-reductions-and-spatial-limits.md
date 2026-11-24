# Strong-migration reductions and spatial limits

When migration is strong compared with drift, a structured population drifts like a single panmictic population. Felsenstein (Section VII.5) shows for the $n$-island model that the population drifts as one panmictic population of size near $Nn$ when $Nm$ is large and that structure impedes the spread of alleles when $Nm$ is small, with the transition near $4Nm = (n - 1)/n$, and reports that Nagylaki (1977) proved that any connected geographic structure behaves as if panmictic when all the $Nm_{ij}$ are large. With genic selection in Wright's island model, Cherry and Wakeley (2003, abstract) relate the subdivided population to a panmictic Wright–Fisher population with a larger effective size and a smaller effective selection coefficient whose product is unchanged.

In the structured diffusion with migration rates multiplied by a large factor $\lambda$, the deme frequencies are pulled towards their weighted average, and the candidate one-dimensional limit for $\bar x = \sum_iw_ix_i$, with $w$ the stationary law of the backward migration chain, has drift $\sum_iw_i\beta_i(\bar x)$ and diffusion coefficient $\sum_iw_i^2\bar x(1 - \bar x)/\kappa_i$, obtained by evaluating the drift and the quadratic-variation rate of $\bar x$ at the equal-frequency configuration.

For populations in a spatial continuum the limits are stochastic partial differential equations, not the deterministic Fisher–KPP equation. Biswas, Etheridge and Klimek (arXiv 2018, Section 1, equations (1.1), (1.2)) obtain, for selection fluctuating between two environments, the one-dimensional equation $dw = \frac12\Delta w\,dt + s^2w(1 - w)(1 - 2w)\,dt + \sqrt{w(1 - w)}\,W(dt, dx) + \sqrt2\,sw(1 - w)\,\tilde W(dt, dx)$ with space-time white noise $W$ for genetic drift, and show that in higher dimensions the drift term vanishes in the limit of the spatial Lambda–Fleming–Viot process.

## Expansion

1. The structured diffusion with migration rates scaled by $\lambda$.
2. Convergence of $\bar x$ as $\lambda \to \infty$ to the one-dimensional diffusion with averaged coefficients, and the collapse of the differences between demes.
3. The effective size and selection coefficient of the island model in this limit.
4. Continuum limits: the one-dimensional stochastic equation with drift noise, and its relation to the deterministic travelling waves of the Fisher–KPP equation obtained when the noise terms are removed.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, course text, University of Washington, Section VII.5 (the island model; discussion around equations (VII-49)–(VII-51)).
- J. L. Cherry and J. Wakeley, A diffusion approximation for selection and drift in a subdivided population, Genetics 163 (2003), 421–428, abstract. <https://doi.org/10.1093/genetics/163.1.421>
- N. Biswas, A. M. Etheridge and A. Klimek, The spatial Lambda-Fleming-Viot process with fluctuating selection, arXiv:1802.08188, Section 1. <https://arxiv.org/abs/1802.08188>
