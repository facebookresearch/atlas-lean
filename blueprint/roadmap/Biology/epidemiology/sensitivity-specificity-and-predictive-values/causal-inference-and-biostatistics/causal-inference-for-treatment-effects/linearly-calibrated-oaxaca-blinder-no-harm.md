# No-harm linear calibration of generalized Oaxaca-Blinder estimators

Work in the completely randomized experiment and notation of the [generalized Oaxaca-Blinder estimator](generalized-oaxaca-blinder-estimator.md), with arbitrary (possibly misspecified, nonlinear) predictors $\hat\mu_0, \hat\mu_1$.

**Linear calibration (eq. 2).** Form the pseudo-features $\tilde x_i = (\hat\mu_0(x_i), \hat\mu_1(x_i))^{\top}$. For each arm $z \in \{0,1\}$ regress observed outcomes on $\tilde x_i$ with an intercept using only units with $Z_i = z$:

$$(\hat\alpha_z, \hat\beta_{z,0}, \hat\beta_{z,1}) \in \arg\min\sum_{i:Z_i = z}\{y_i(z) - \alpha_z - \beta_{z,0}\hat\mu_0(x_i) - \beta_{z,1}\hat\mu_1(x_i)\}^2,$$

set $\hat\mu_{\mathrm{OLS},z}(x_i) = \hat\alpha_z + \hat\beta_{z,0}\hat\mu_0(x_i) + \hat\beta_{z,1}\hat\mu_1(x_i)$, and let $\hat\tau_{\mathrm{cal}}$ be the generalized Oaxaca-Blinder estimator built from $\hat\mu_{\mathrm{OLS},0}, \hat\mu_{\mathrm{OLS},1}$. Equivalently, $\hat\tau_{\mathrm{cal}}$ is Lin's interacted regression-adjusted estimator with covariates $\tilde x_i$.

Throughout, assume nonvanishing allocation fractions $n_z/N \to p_z \in (0, 1)$, as in the [asymptotic regime](generalized-oaxaca-blinder-estimator.md) of the uncalibrated estimator, and design nondegeneracy: the limiting covariance matrix of the pseudo-features $(\dot\mu_0(x_i), \dot\mu_1(x_i))$ is nonsingular, so that the arm-wise regression coefficients converge.

**Theorem 1.** Under these conditions and stability, vanishing error processes, limiting means and variances, and bounded fourth moments (Assumptions 1, 2, 4, 5), $N^{1/2}(\hat\tau_{\mathrm{cal}} - \tau_{\mathrm{SATE}})$ converges in distribution to a mean-zero Gaussian (degenerate if its limiting variance is zero), and its asymptotic variance is no larger than that of $N^{1/2}(\hat\tau_{\mathrm{unadj}} - \tau_{\mathrm{SATE}})$.

**Theorem 2.** Under the same assumptions, the asymptotic variance of $N^{1/2}(\hat\tau_{\mathrm{cal}} - \tau_{\mathrm{SATE}})$ is no larger than that of the singly calibrated estimator of Guo and Basse (which regresses arm $z$ only on $\hat\mu_z$), and, if also prediction unbiasedness (Assumption 3) holds for $\hat\mu_z$, no larger than that of the uncalibrated $\hat\tau_{\mathrm{gOB}}$.

**Theorem 3.** Under the assumptions of Theorem 1, let $\hat\pi(\tilde x_i)$ be fitted probabilities from a logistic regression of $Z_i$ on an intercept and $\tilde x_i$, and $\hat\tau_{\mathrm{ipw}} = N^{-1}\sum_i Z_iy_i(Z_i)/\hat\pi(\tilde x_i) - N^{-1}\sum_i(1-Z_i)y_i(Z_i)/\{1 - \hat\pi(\tilde x_i)\}$. Then $N^{1/2}(\hat\tau_{\mathrm{cal}} - \hat\tau_{\mathrm{ipw}}) = o_p(1)$.

## Expansion

The intercepts force prediction unbiasedness, so $\hat\tau_{\mathrm{cal}}$ is a standardization estimator. Lin's (2013) theorem shows that interacted OLS adjustment is asymptotically no worse than the difference in means, and also no worse than any other fixed linear adjustment using the same covariates. Including both $\hat\mu_0$ and $\hat\mu_1$ among the regressors places the unadjusted, uncalibrated and singly calibrated estimators inside the class over which the calibrated one is optimal. The proof extends Lin's argument to the data-dependent covariates $\tilde x_i$, using stability and the vanishing error process to replace $\hat\mu_z$ by the fixed limits $\dot\mu_z$. Theorem 3 says the same gain comes from inverse-probability weighting with a propensity model fitted on predicted potential outcomes, which corrects chance imbalance in exactly the directions that predict outcomes.

## Depends on

- [Generalized Oaxaca-Blinder imputation estimator](generalized-oaxaca-blinder-estimator.md)

## Sources

- P. L. Cohen and C. B. Fogarty, *No-harm calibration for generalized Oaxaca-Blinder estimators*, Biometrika (2024). <https://doi.org/10.1093/biomet/asad036>
- W. Lin, *Agnostic notes on regression adjustments to experimental data: reexamining Freedman's critique*, Ann. Appl. Stat. 7 (2013), 295-318. <https://doi.org/10.1214/12-AOAS583>
