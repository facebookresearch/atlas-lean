# Asymptotic law of the dose slope under shared multiplicative error

**Setting.** True doses follow the SUMA model $X_i = Z_i\epsilon_{SM}\epsilon_{M,i} + \epsilon_{SA} + \epsilon_{A,i}$, $1 \le i \le n$, with all errors independent, $E\epsilon_{SM} = E\epsilon_{M,i} = 1$, $E\epsilon_{SA} = E\epsilon_{A,i} = 0$, $\operatorname{Var}\epsilon_{M,i} = \sigma_M^2$, $\operatorname{Var}\epsilon_{A,i} = \sigma_A^2$, and known means $Z_i = E X_i$. Responses follow $Y_i = a + bX_i + \epsilon_i$ with independent $\epsilon_i$, $E\epsilon_i = 0$, $\operatorname{Var}\epsilon_i = \sigma^2$. Let $\hat b_n$ be the least-squares (normal MLE) slope computed from the $Z_i$.

**Theorem.**
1. If $\sigma_M^2 = 0$, $E(Z^2) < \infty$ and $\max_i Z_i = o_p(n^{1/2})$, then

$$\hat b_n \approx_d b\,\epsilon_{SM} + N, \qquad N \sim \mathcal N\Big(0, \frac{\sigma^2 + \sigma_A^2}{n\operatorname{Var}(Z)}\Big),\; N \perp \epsilon_{SM}.$$

2. If $\sigma_M^2 > 0$, $E(Z^4) < \infty$ and $\max_i Z_i^2 = o_p(n^{1/2})$, then

$$\hat b_n \approx_d b\,\epsilon_{SM}N' + N, \qquad N' \sim \mathcal N\Big(1, \frac{E[Z^2(Z - EZ)^2]}{n\operatorname{Var}(Z)^2}\sigma_M^2\Big),$$

with $N$ as above and $\epsilon_{SM}, N', N$ independent.

**Inference rule ($bL+N$).** Approximate the law of the dose-effect estimate in an ERR model by $b_1L + N$, with $L$ lognormal, $EL = 1$, $N$ normal, $EN = 0$, and match $\operatorname{Var}(\hat b_1) = b_1^2\operatorname{Var}(L) + \operatorname{Var}(N)$ to the SUMA-corrected variance. The confidence limits $b_{1,l}, b_{1,u}$ solve

$$\Pr(b_{1,l}L + N \ge \hat b_1) = \alpha/2, \qquad \Pr(b_{1,u}L + N \le \hat b_1) = \alpha/2.$$

## Depends on

- [Poisson excess relative risk model and the SUMA-corrected variance](poisson-excess-relative-risk-model-and-suma-corrected-variance.md)
- [Log-normal distribution](../../../../Probability/distributions/continuous/log-normal-distribution/log-normal-measure.md)

## Proof depends on

- [Lindeberg–Feller central limit theorem](../../../../Probability/central-limit-theorems/lindeberg-feller-central-limit-theorem/lindeberg-feller-clt-triangular.md)

## Expansion

Conditionally on the shared factor, the regression of $Y$ on $Z$ has slope $b\epsilon_{SM}$ (times a near-one factor from unshared multiplicative error), and Lindeberg's central limit theorem under the max-dose conditions gives the normal fluctuation $N$ from the residual and unshared additive noise. Shared multiplicative error therefore does not average out: it rescales the slope by a random factor, so the estimator's spread grows proportionally to $b$. Because $L > 0$, $\Pr(bL + N \le \hat b_1) \to 0$ as $b \to \infty$, so the resulting intervals are always bounded, unlike score-type intervals; parameters other than the dose slope are unaffected by a pure rescaling of dose and keep normal intervals with corrected variances.

## Sources

- Z. Zhang, D. L. Preston, M. Sokolnikov, B. A. Napier, M. Degteva, B. Moroz, V. Vostrotin, E. Shiskina, A. Birchall, D. O. Stram, "Correction of confidence intervals in excess relative risk models using Monte Carlo dosimetry systems with shared errors", PLoS ONE 12(4) (2017) e0174641, Theorem 1 and Eqs (5)–(6) and the corrected confidence-interval construction, <https://doi.org/10.1371/journal.pone.0174641>, PMCID PMC5378348.
