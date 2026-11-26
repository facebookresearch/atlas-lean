# Moran theorem for linear autoregressive populations

**Setting.** Let two populations, at locations $n = 1, 2$, have (log-)abundance deviations following the same first-order autoregression

$$x_n(t+1) = a\, x_n(t) + \varepsilon_n(t), \qquad |a| < 1,$$

where the environmental noise vectors $(\varepsilon_1(t), \varepsilon_2(t))$, $t \in \mathbb{Z}$, are independent and identically distributed across $t$, with mean zero, variances $\sigma_1^2, \sigma_2^2 > 0$ and covariance $c_{12} = \mathrm{Cov}(\varepsilon_1(t), \varepsilon_2(t))$.

**Theorem (Moran 1953).** In the stationary regime,

$$\mathrm{Var}\, x_n = \frac{\sigma_n^2}{1 - a^2}, \qquad \mathrm{Cov}(x_1, x_2) = \frac{c_{12}}{1 - a^2}, \qquad \mathrm{Corr}(x_1(t), x_2(t)) = \mathrm{Corr}(\varepsilon_1(t), \varepsilon_2(t)).$$

That is, populations with identical linear density dependence inherit exactly the spatial correlation of their environmental drivers.

**Corollary (interacting drivers).** Suppose each driver is a combination of two environmental variables, $\varepsilon_n(t) = u\,\alpha_n(t) + w\,\beta_n(t)$, with $(\alpha_1, \alpha_2, \beta_1, \beta_2)(t)$ i.i.d. over $t$ with mean zero. Then

$$\mathrm{Corr}(x_1, x_2) = \frac{u^2\, \mathrm{Cov}(\alpha_1, \alpha_2) + w^2\, \mathrm{Cov}(\beta_1, \beta_2) + u w \big(\mathrm{Cov}(\alpha_1, \beta_2) + \mathrm{Cov}(\beta_1, \alpha_2)\big)}{\sqrt{\mathrm{Var}(\varepsilon_1)\, \mathrm{Var}(\varepsilon_2)}},$$

with $\mathrm{Var}(\varepsilon_n) = u^2 \mathrm{Var}\,\alpha_n + w^2 \mathrm{Var}\,\beta_n + 2uw\, \mathrm{Cov}(\alpha_n, \beta_n)$. The resulting synchrony is not determined by the synchrony of each driver alone: the cross-covariance terms between drivers (interaction effects) can raise or lower it.

## Expansion

Iterating the recursion gives the stationary moving-average representation $x_n(t) = \sum_{s \ge 0} a^s \varepsilon_n(t - 1 - s)$, which converges in mean square since $|a| < 1$. Independence across times kills all cross terms with different lags, so $\mathrm{Cov}(x_1, x_2) = c_{12} \sum_{s \ge 0} a^{2s} = c_{12}/(1 - a^2)$ and similarly for the variances; the common factor $1/(1-a^2)$ cancels in the correlation. The corollary is bilinearity of covariance applied to $\varepsilon_n = u\alpha_n + w\beta_n$. The identity fails if the two populations have different autoregression coefficients or nonlinear dynamics, and it is a statement about population correlations, so short sampled series estimate it only approximately.

## Sources

- L. W. Sheppard, E. J. Defriez, P. C. Reid and D. C. Reuman, "Synchrony is more than its top-down and climatic parts: interacting Moran effects on phytoplankton in British seas", PLoS Computational Biology 15 (2019), e1006744, Introduction and Appendix S1, <https://doi.org/10.1371/journal.pcbi.1006744> (PMCID: PMC6438443).
- P. A. P. Moran, "The statistical analysis of the Canadian lynx cycle. II. Synchronization and meteorology", Australian Journal of Zoology 1 (1953), 291–298.
