# Modified Egger intercept test for directional and correlated pleiotropy

**Setting (two-sample summary-data Mendelian randomization).** For independent SNPs $j = 1, \dots, p$, the SNP–outcome effect is $\Gamma_j = \beta\gamma_j + \alpha_j$, where $\beta$ is the causal effect, $\gamma_j$ the SNP–exposure effect and $\alpha_j$ the pleiotropic effect. Write $\mu_\alpha$ for the mean of the $\alpha_j$ and $\rho_{\gamma,\alpha}$ for the correlation between the $\gamma_j$ and the $\alpha_j$ (nonzero under correlated pleiotropy, i.e. failure of InSIDE). Assume:

1. the exposure and outcome GWAS sample sizes diverge at the same rate and $p \to \infty$;
2. the pairs $(\hat\Gamma_j, \hat\gamma_j)$ are mutually independent across $j$, with $\hat\Gamma_j \sim N(\beta\gamma_j + \alpha_j, \sigma_{Y_j}^2)$ independent of $\hat\gamma_j \sim N(\gamma_j, \sigma_{X_j}^2)$, known variances, and a common scale $\nu \to 0$ such that $\sigma_{X_j}/\nu$ and $\sigma_{Y_j}/\nu$ are bounded and bounded away from zero;
3. the $\alpha_j$ are independent with variance $\tau_\alpha^2$, bounded third moment and $\tau_\alpha/\nu$ bounded;
4. (no dominant instrument) $\max_{j \in \mathcal{S}_\lambda} (\gamma_j - \bar\gamma_\lambda)^2 / \sum_{j \in \mathcal{S}_\lambda} (\gamma_j - \bar\gamma_\lambda)^2 \to 0$ in probability.

The null hypothesis of the Egger intercept test is $H_0: \mu_\alpha = 0$ and $\rho_{\gamma,\alpha} = 0$ (no directional and no correlated pleiotropy).

**Statistic.** Select SNPs by the rerandomized rule $\mathcal{S}_\lambda = \{ j : |\hat\gamma_j/\sigma_{X_j} + Z_j| > \lambda \}$ with independent pseudo-noise $Z_j \sim N(0, \eta^2)$; let $p_\lambda = |\mathcal{S}_\lambda|$, let $\hat\gamma_{j,\mathrm{RB}}$ be the Rao–Blackwellized selection-unbiased SNP–exposure estimate with unbiased variance estimate $\hat\sigma^2_{X_j,\mathrm{RB}}$, and let $\hat\beta_{\mathrm{R}}$ be the rerandomized IVW estimator. With all sums over $j \in \mathcal{S}_\lambda$, define

$$

\hat\Lambda_{\mathrm{R,C}} = \sum_j \frac{\hat\Gamma_j}{\sigma_{Y_j}^2} \sum_j \frac{\hat\gamma_{j,\mathrm{RB}}^2 - \hat\sigma^2_{X_j,\mathrm{RB}}}{\sigma_{Y_j}^2} - \sum_j \frac{\hat\gamma_{j,\mathrm{RB}}\hat\Gamma_j}{\sigma_{Y_j}^2} \sum_j \frac{\hat\gamma_{j,\mathrm{RB}}}{\sigma_{Y_j}^2} + \sum_j \frac{\hat\sigma^2_{X_j,\mathrm{RB}}\, \hat\Gamma_j}{\sigma_{Y_j}^4},

$$

the numerator of the bias-corrected Egger intercept plus a correction that makes its conditional mean exactly zero under $H_0$, and the variance estimate $\hat V_{\mathrm{R,C}} = \sum_j \sigma_{Y_j}^{-4} \hat u_j^2$, where

$$

\hat u_j = \big(\hat\Gamma_j - \hat\beta_{\mathrm{R}} \hat\gamma_{j,\mathrm{RB}}\big) \sum_k \frac{\hat\gamma_{k,\mathrm{RB}}^2 - \hat\sigma^2_{X_k,\mathrm{RB}}}{\sigma_{Y_k}^2} - \Big[\hat\gamma_{j,\mathrm{RB}}\hat\Gamma_j - \hat\beta_{\mathrm{R}}\big(\hat\gamma_{j,\mathrm{RB}}^2 - \hat\sigma^2_{X_j,\mathrm{RB}}\big)\Big] \sum_k \frac{\hat\gamma_{k,\mathrm{RB}}}{\sigma_{Y_k}^2}.

$$

The modified Egger intercept (MEI) statistic is $Z_{\mathrm{ME}} = \hat\Lambda_{\mathrm{R,C}} / \sqrt{\hat V_{\mathrm{R,C}}}$.

**Theorem.** Under assumptions 1–4, with $p_\lambda \to \infty$ and $\kappa_\lambda \sqrt{p_\lambda} \to \infty$ in probability, where $\kappa_\lambda = p_\lambda^{-1} \sum_{j \in \mathcal{S}_\lambda} \gamma_j^2/\sigma_{X_j}^2$ is the average instrument strength, under $H_0$

$$

Z_{\mathrm{ME}} \xrightarrow{d} N(0,1).

$$

The selection threshold $\lambda$ may stay fixed, so many weak instruments are allowed.

**Power and allele coding.** Under the alternative, $E(\hat\Lambda_{\mathrm{R,C}} \mid \mathcal{S}_\lambda)$ is proportional to $\mu_{\alpha|\mathcal{S}_\lambda} \tau^2_{\gamma|\mathcal{S}_\lambda} - \rho_{\gamma,\alpha|\mathcal{S}_\lambda} \mu_{\gamma|\mathcal{S}_\lambda} \tau_{\alpha|\mathcal{S}_\lambda} \tau_{\gamma|\mathcal{S}_\lambda}$ (means, standard deviations and correlation over the selected SNPs), which depends on SNP orientation. Under major-allele coding with SNP–exposure effects symmetric about zero, $\mu_{\gamma|\mathcal{S}_\lambda} = 0$ and the test detects only directional pleiotropy; under all-positive coding (exposure-increasing allele as effect allele) and the same symmetry, directional effects cancel and the test targets correlated pleiotropy. The two $Z$-scores are asymptotically bivariate normal under $H_0$, and $\max(|Z^{\mathrm M}_{\mathrm{ME}}|, |Z^{\mathrm P}_{\mathrm{ME}}|)$ with an estimated correlation gives a combined test.

## Expansion

The ordinary Egger intercept $\hat\mu_{\alpha,\mathrm{E}} = \sum_j \sigma_{Y_j}^{-2}(\hat\Gamma_j - \hat\beta_{\mathrm E}\hat\gamma_j) / \sum_j \sigma_{Y_j}^{-2}$ inherits measurement-error and winner's-curse bias from the Egger slope, which inflates type I error. Replacing the slope by the rerandomized IVW estimator, which is consistent under $H_0$ and corrects both biases, and the SNP–exposure estimates by their Rao–Blackwellized versions removes the bias. Because $E(\hat\Lambda_{\mathrm R} \mid \mathcal{S}_\lambda) = -\sum_j \sigma_{Y_j}^{-4}\sigma^2_{X_j,\mathrm{RB}}\Gamma_j$ under $H_0$, the last term in $\hat\Lambda_{\mathrm{R,C}}$ cancels it. The statistic is asymptotically a sum of conditionally independent, mean-zero terms $\sigma_{Y_j}^{-2}u_j$; a Lindeberg central limit theorem, consistency of $\hat\beta_{\mathrm R}$ and consistency of the sum-of-squares variance estimator give the normal limit.

## Depends on

- [MR-Egger intercept](egger-intercept.md)

## Sources

- Yilei Ma, Youpeng Su, Xin Liu, Xuanye Cui, Siqi Xu, Ping Yin, Peng Wang, "Modified Egger Intercept Tests for Detecting Horizontal Pleiotropy in Two-Sample Summary-Data Mendelian Randomization," arXiv 2026. Section 2 (Assumptions 1–3), Section 4 (MEI statistic, Assumption 4, Theorem 1, allele-coding strategies and combined test); appendix lemmas on the rerandomized IVW estimator. <https://doi.org/10.48550/arXiv.2605.28471>
