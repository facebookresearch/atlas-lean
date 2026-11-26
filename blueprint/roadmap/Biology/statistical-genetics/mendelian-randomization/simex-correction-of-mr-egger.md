# SIMEX correction of the MR-Egger slope

In the two-sample summary-data model of [MR-Egger regression dilution](regression-dilution-of-mr-egger-and-the-i2-gx-statistic.md), the MR-Egger slope $\hat\beta_{1E}$ is attenuated by roughly $I^2_{GX}$ when the SNP–exposure estimates $\hat\gamma_j$ carry error variances $\sigma_{Xj}^2$.

**Simulation extrapolation (SIMEX).** For a grid of $\lambda \ge 0$:

1. For $b = 1, \dots, B$, draw $\tilde\gamma_j^{(b)}(\lambda) \sim N(\hat\gamma_j, \lambda\sigma_{Xj}^2)$ independently, so that the simulated exposure estimates have total error variance $(1 + \lambda)\sigma_{Xj}^2$ about $\gamma_j$.
2. Refit MR-Egger of $\hat\Gamma_j$ on $\tilde\gamma_j^{(b)}(\lambda)$ and average the slopes to get $\bar\beta_{1E}(\lambda)$.

Fit a smooth extrapolant (the paper's application uses a quadratic) to the points $(\lambda, \bar\beta_{1E}(\lambda))$ and evaluate it at $\lambda = -1$. That value is the SIMEX estimate, an estimate of the slope with zero measurement error, i.e. under NOME. Existing SIMEX software supplies point estimates and standard errors for inference after adjustment.

The naive correction $\hat\beta_{1E}/I^2_{GX}$ is not recommended. The estimate of $I^2_{GX}$ is itself random and can be near or equal to zero even when the true value is large, so the ratio is unstable.

## Depends on

- [Regression dilution of MR-Egger and the $I^2_{GX}$ statistic](regression-dilution-of-mr-egger-and-the-i2-gx-statistic.md)

## Expansion

Under classical measurement error the attenuated slope is a smooth function of the error-variance multiplier, approximately $\beta\,\sigma_\gamma^2/(\sigma_\gamma^2 + (1+\lambda)s^2)$. At $\lambda = 0$ it is the observed estimate, it decreases as $\lambda$ grows, and $\lambda = -1$ corresponds to no error. Simulation traces this curve for $\lambda \ge 0$, where data can be generated, and extrapolation recovers the unobservable point $\lambda = -1$. The choice of extrapolant introduces some residual bias. In the paper's simulations with strong instruments (mean $F = 125$), SIMEX mitigated the slope bias and reduced the inflated type I error of the pleiotropy test, leaving the power for the causal effect unchanged. With weaker instruments (mean $F = 20$) it corrected less of the bias, and under the causal null it slightly raised the type I error, so adjusting can be worse than not adjusting. The paper recommends reporting $I^2_{GX}$ with every MR-Egger analysis. When $I^2_{GX} < 90\%$, MR-Egger point estimates should be read with caution and SIMEX run as a sensitivity analysis.

## Sources

- J. Bowden, F. Del Greco M, C. Minelli, G. Davey Smith, N. A. Sheehan and J. R. Thompson, "Assessing the suitability of summary data for two-sample Mendelian randomization analyses using MR-Egger regression: the role of the I² statistic", *International Journal of Epidemiology* 45(6) (2016), 1961–1974, <https://doi.org/10.1093/ije/dyw220> (PMC5446088), Methods section "Bias adjustment via simulation extrapolation", Results and Discussion; technical details in the Supplementary Appendix.
