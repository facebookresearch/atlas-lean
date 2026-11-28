# Adjusted Cochran's Q for pleiotropy in multivariable Mendelian randomization

In two-sample multivariable MR with two exposures and $L$ mutually uncorrelated variants (so that the SNP association estimates are independent across variants), let $\hat\Gamma_j$ be the SNP–outcome estimate with variance $\sigma_{yj}^2$, let $\hat\pi_{1j}, \hat\pi_{2j}$ be the SNP–exposure estimates with variances $\sigma_{1j}^2, \sigma_{2j}^2$ and covariance $\sigma_{12j}$, and let $\hat\beta_1, \hat\beta_2$ be efficient estimates of the direct effects, for example from the multivariable IVW fit. Define

$$Q_A = \sum_{j=1}^{L}\frac{\big(\hat\Gamma_j - \hat\beta_1\hat\pi_{1j} - \hat\beta_2\hat\pi_{2j}\big)^2}{\sigma_{Aj}^2}, \qquad \sigma_{Aj}^2 = \sigma_{yj}^2 + \hat\beta_1^2\sigma_{1j}^2 + \hat\beta_2^2\sigma_{2j}^2 + 2\hat\beta_1\hat\beta_2\sigma_{12j}.$$

Under the null hypothesis that no variant has a pleiotropic effect on the outcome, so that all variants are valid instruments for the two exposures, $Q_A$ is asymptotically $\chi^2_{L-2}$; the source assumes throughout that the variants "are mutually uncorrelated (by design)", and the law fails for correlated variants. Excess heterogeneity ("heterogeneity is bad") is evidence of invalid instruments. The test is global: it does not say which variants are invalid.

The standard Cochran statistic, which weights only by $\sigma_{yj}^2$, ignores the uncertainty in the exposure estimates and is not asymptotically $\chi^2$. $Q_A$ is the multivariable extension of the adjusted univariable Q statistic, and the paper suggests updating the weights iteratively from the current causal estimates.

## Expansion

For valid instruments, $\hat\Gamma_j - \beta_1\hat\pi_{1j} - \beta_2\hat\pi_{2j}$ has mean zero. Its variance is $\sigma_{yj}^2$ plus the delta-method contribution of the exposure estimates, $\beta_1^2\sigma_{1j}^2 + \beta_2^2\sigma_{2j}^2 + 2\beta_1\beta_2\sigma_{12j}$, the outcome sample being independent of the exposure samples. Standardizing and summing gives approximately $\chi^2_L$, and estimating two parameters removes two degrees of freedom. A pleiotropic $\alpha_j \ne 0$ adds a nonzero mean to the $j$th residual. When the covariances $\sigma_{12j}$ are unknown, setting them to zero is a good approximation whenever $\hat\beta_1\hat\beta_2\sigma_{12j}$ is small. In the paper's simulation with $100$ variants, $Q_A$ follows $\chi^2_{98}$ under the null while the unadjusted Q does not.

## Sources

- E. Sanderson, G. Davey Smith, F. Windmeijer and J. Bowden, "An examination of multivariable Mendelian randomization in the single-sample and two-sample summary data settings", *International Journal of Epidemiology* 48(3) (2019), 713–727, <https://doi.org/10.1093/ije/dyy262> (PMC6734942), section "Testing instrument validity: heterogeneity is 'bad'" (Equation 13, Figure 6) and "Approximating $Q_{x1}$, $Q_{x2}$ and $Q_A$ with incomplete information".
