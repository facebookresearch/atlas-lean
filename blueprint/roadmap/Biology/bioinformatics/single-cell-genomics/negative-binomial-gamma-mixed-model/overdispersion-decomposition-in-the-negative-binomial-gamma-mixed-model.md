# Overdispersion decomposition in the negative binomial gamma mixed model

For cell $j$ of subject $i$, let $y_{ij}$ be a gene's raw count, $x_{ij} \in \mathbb{R}^{k+1}$ fixed-effect predictors, $\pi_{ij} > 0$ a known scaling factor (library size), $\beta$ the coefficients and $\phi > 0$ the cell-level dispersion. The **negative binomial gamma mixed model** (NBGMM) is

$$y_{ij} \mid \omega_i \sim \mathrm{NB}\big(\mu_{ij} = \pi_{ij}\, e^{x_{ij}^T \beta}\, \omega_i,\ \phi\big), \qquad \operatorname{Var}(y_{ij} \mid \omega_i) = \mu_{ij} + \mu_{ij}^2/\phi,$$

with independent subject effects $\omega_i \sim \mathrm{Gamma}(\alpha, \lambda)$ (shape $\alpha$, rate $\lambda$) parametrized by a variance component $\sigma^2 > 0$ through

$$\alpha = \frac{1}{e^{\sigma^2} - 1}, \qquad \lambda = \frac{1}{e^{\sigma^2/2}(e^{\sigma^2} - 1)} .$$

**Proposition.** (i) $\omega_i$ has the same mean $e^{\sigma^2/2}$ and variance $e^{\sigma^2}(e^{\sigma^2} - 1)$ as a log-normal $\exp(N(0, \sigma^2))$ effect. (ii) The marginal moments are

$$\mathbb{E}(y_{ij}) = \pi_{ij}\, e^{x_{ij}^T\beta + \sigma^2/2}, \qquad \operatorname{Var}(y_{ij}) = \mathbb{E}(y_{ij}) + \mathbb{E}(y_{ij})^2 \big(e^{\sigma^2} - 1\big) + \mathbb{E}(y_{ij})^2\, \frac{e^{\sigma^2}}{\phi},$$

so the first overdispersion term depends on the subject-level variance component alone, while the second combines cell-level dispersion $\phi$ with $\sigma^2$.

## Expansion

For (i), a $\mathrm{Gamma}(\alpha, \lambda)$ variable has mean $\alpha/\lambda = e^{\sigma^2/2}$ and variance $\alpha/\lambda^2 = e^{\sigma^2}(e^{\sigma^2} - 1)$, matching the log-normal moments. For (ii), write $c = \pi_{ij} e^{x_{ij}^T\beta}$ and $m = c\,\mathbb{E}\omega_i$. The law of total variance gives $\operatorname{Var}(y) = \mathbb{E}[c\omega + c^2\omega^2/\phi] + c^2 \operatorname{Var}\omega = m + c^2 \mathbb{E}[\omega^2]/\phi + c^2 \operatorname{Var}\omega$; using $\operatorname{Var}\omega/(\mathbb{E}\omega)^2 = e^{\sigma^2} - 1$ and $\mathbb{E}[\omega^2]/(\mathbb{E}\omega)^2 = e^{\sigma^2}$ yields the formula. Moment matching to the negative binomial log-normal mixed model makes the gamma version a good surrogate when $\sigma^2$ is not large, while the gamma effect is conjugate to Poisson sampling, which NEBULA exploits for a fast approximate marginal likelihood.

## Sources

- L. He, J. Davila-Velderrain, T. S. Sumida, D. A. Hafler, M. Kellis and A. M. Kulminski, "NEBULA is a fast negative binomial mixed model for differential or co-expression analysis of large-scale multi-subject single-cell data", Communications Biology 4 (2021), Methods "The model specification in NEBULA", Eqs. (1)–(4), <https://doi.org/10.1038/s42003-021-02146-6>, PMCID PMC8155058.
