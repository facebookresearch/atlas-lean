# Conjugate Poisson–gamma subject likelihood

In the [negative binomial gamma mixed model](overdispersion-decomposition-in-the-negative-binomial-gamma-mixed-model.md), write the negative binomial as a Poisson–gamma mixture: $y_{ij} \mid \omega_i, \upsilon_{ij} \sim \mathrm{Poisson}(\omega_i \upsilon_{ij} c_{ij})$ with $c_{ij} = \pi_{ij} e^{x_{ij}^T\beta}$, cell-level $\upsilon_{ij} \sim \mathrm{Gamma}(\phi, \phi)$ and subject-level $\omega_i \sim \mathrm{Gamma}(\alpha, \lambda)$, all independent.

**Proposition.** Conditionally on the cell-level effects $\upsilon_i = (\upsilon_{i1}, \dots, \upsilon_{in_i})$, the likelihood of subject $i$'s counts after integrating out $\omega_i$ is

$$\int_0^\infty \prod_{j=1}^{n_i} \frac{e^{-\omega c_{ij}\upsilon_{ij}} (\omega c_{ij}\upsilon_{ij})^{y_{ij}}}{y_{ij}!}\, \frac{\lambda^\alpha \omega^{\alpha - 1} e^{-\lambda\omega}}{\Gamma(\alpha)}\, d\omega = \frac{\lambda^\alpha\, \Gamma(Y_i + \alpha)}{\Gamma(\alpha) \prod_j y_{ij}!} \prod_{j} (c_{ij}\upsilon_{ij})^{y_{ij}}\, \Big(\lambda + \sum_j c_{ij}\upsilon_{ij}\Big)^{-(Y_i + \alpha)},$$

where $Y_i = \sum_j y_{ij}$. Moreover, $\omega_i \mid y_i, \upsilon_i \sim \mathrm{Gamma}\big(\alpha + Y_i,\ \lambda + \sum_j c_{ij}\upsilon_{ij}\big)$. Setting all $\upsilon_{ij} = 1$ gives the closed-form (negative multinomial) likelihood of the Poisson gamma mixed model; the full NBGMM likelihood is the expectation of this expression over the $\upsilon_{ij}$.

## Depends on

- [Overdispersion decomposition in the negative binomial gamma mixed model](overdispersion-decomposition-in-the-negative-binomial-gamma-mixed-model.md)

## Proof depends on

- [Pooled Gamma–Poisson conjugacy](../../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/pooled-posterior-eq-gamma-pdfreal.md)

## Expansion

The integrand is $\frac{\lambda^\alpha}{\Gamma(\alpha)\prod_j y_{ij}!} \prod_j (c_{ij}\upsilon_{ij})^{y_{ij}}\, \omega^{Y_i + \alpha - 1} e^{-(\lambda + \sum_j c_{ij}\upsilon_{ij})\omega}$, and $\int_0^\infty \omega^{a-1} e^{-b\omega} d\omega = \Gamma(a) b^{-a}$ gives the result; the integrand normalized by this constant is the stated gamma posterior. Mixing each Poisson over $\upsilon_{ij} \sim \mathrm{Gamma}(\phi, \phi)$ recovers $\mathrm{NB}(\mu, \phi)$ with variance $\mu + \mu^2/\phi$. The remaining integral over the $\upsilon_{ij}$ has no closed form; NEBULA approximates it when the number of cells per subject is large (NEBULA-LN) and otherwise switches to an h-likelihood with a Laplace approximation (NEBULA-HL), reaching convergence in a few Newton steps instead of a two-layer GLMM optimization.

## Sources

- L. He, J. Davila-Velderrain, T. S. Sumida, D. A. Hafler, M. Kellis and A. M. Kulminski, "NEBULA is a fast negative binomial mixed model for differential or co-expression analysis of large-scale multi-subject single-cell data", Communications Biology 4 (2021), Methods "Approximation of marginal likelihood in NEBULA-LN", Eqs. (5)–(6), <https://doi.org/10.1038/s42003-021-02146-6>, PMCID PMC8155058.
