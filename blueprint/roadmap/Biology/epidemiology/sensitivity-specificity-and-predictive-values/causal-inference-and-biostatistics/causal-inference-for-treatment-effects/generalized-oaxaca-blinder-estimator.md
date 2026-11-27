# Generalized Oaxaca-Blinder imputation estimator in a completely randomized experiment

A finite population of $N$ units has fixed potential outcomes $y_i(0), y_i(1)$ and covariates $x_i \in \mathbb{R}^k$. A [completely randomized experiment](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md) draws the assignment $Z \in \{0,1\}^N$ uniformly among vectors with $n_1$ treated and $n_0 = N - n_1$ controls, and reveals $y_i(Z_i)$. The estimand is the sample [average treatment effect](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md) $\tau_{\mathrm{SATE}} = N^{-1}\sum_{i=1}^N\{y_i(1) - y_i(0)\}$; the unadjusted estimator is the difference in means $\hat\tau_{\mathrm{unadj}} = n_1^{-1}\sum_i Z_iy_i(Z_i) - n_0^{-1}\sum_i(1-Z_i)y_i(Z_i)$.

**Definition (eq. 1).** Given prediction functions $\hat\mu_0, \hat\mu_1$ for the control and treated outcomes, impute

$$\hat y_i(z) = \begin{cases} y_i(Z_i) & Z_i = z,\\ \hat\mu_z(x_i) & Z_i \ne z,\end{cases} \qquad \hat\tau_{\mathrm{gOB}} = N^{-1}\sum_{i=1}^N\{\hat y_i(1) - \hat y_i(0)\}.$$

The difference in means and Lin's regression-adjusted estimator are special cases.

**Prediction unbiasedness (Assumption 3).** If $\sum_{i:Z_i = z}\hat\mu_z(x_i) = \sum_{i:Z_i = z}y_i(Z_i)$ for $z = 0, 1$ (true, for example, for generalized linear models with an intercept fitted by maximum likelihood with canonical link), then

$$\hat\tau_{\mathrm{gOB}} = N^{-1}\sum_{i=1}^N\{\hat\mu_1(x_i) - \hat\mu_0(x_i)\},$$

a model-standardization estimator.

**Asymptotic regime.** Along a sequence of finite populations with $N \to \infty$, assume nonvanishing allocation, $n_z/N \to p_z \in (0, 1)$ for $z = 0, 1$ (complete randomization alone allows, for example, a single treated unit for every $N$, and then none of the conclusions below holds), and (1) stability: deterministic $\dot\mu_z$ with $\{N^{-1}\sum_i\|\dot\mu_z(x_i) - \hat\mu_z(x_i)\|^2\}^{1/2} = o_p(1)$; (2) vanishing error process: $|G_{N,z}(\dot\mu_z) - G_{N,z}(\hat\mu_z)| = o_P(1)$, where $G_{N,z}(f) = N^{-1/2}\sum_i f(x_i)\{\mathbb{1}(Z_i = z)/(n_z/N) - 1\}$; (4) limiting means and covariances of $(y_i(0), y_i(1), \dot\mu_0(x_i), \dot\mu_1(x_i))$; (5) bounded fourth moments. Under nonvanishing allocation, assumptions 1-3 give consistency and an asymptotically linear representation in terms of residuals $y_i(z) - \dot\mu_z(x_i)$ (Guo and Basse, 2023, Theorem 2); with (4)-(5) the representation has a Gaussian limit, which is nondegenerate when its limiting variance, a function of the limiting residual covariances, is positive.

## Depends on

- [Expectation of a statistic under complete randomization](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/rand-exp.md)
- [Finite-population average treatment effect](../../../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md)

## Expansion

When $Z_i = z$ the imputation is the observed outcome, so $\hat\tau_{\mathrm{gOB}}$ adds to the difference in means a correction $N^{-1}\sum_i[(1-Z_i)\hat\mu_1(x_i) - Z_i\hat\mu_0(x_i)]$ and its counterpart. Under prediction unbiasedness the observed and predicted sums agree within each arm, collapsing the estimator to standardization. These assumptions do not ensure that the adjustment helps: with a misspecified nonlinear model (the source gives a Poisson-regression example) $\hat\tau_{\mathrm{gOB}}$ can have larger asymptotic variance than $\hat\tau_{\mathrm{unadj}}$, which motivates [linear calibration](linearly-calibrated-oaxaca-blinder-no-harm.md).

## Sources

- P. L. Cohen and C. B. Fogarty, *No-harm calibration for generalized Oaxaca-Blinder estimators*, Biometrika (2024). <https://doi.org/10.1093/biomet/asad036>
- K. Guo and G. Basse, *The generalized Oaxaca-Blinder estimator*, J. Amer. Statist. Assoc. (2023). <https://doi.org/10.1080/01621459.2021.1941053>
