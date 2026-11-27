# Median-initialized adaptive Lasso for some invalid instruments

In Mendelian randomization with individual-level data, consider $n$ observations of an outcome $y$, an exposure $d$ and $L$ genetic instruments $Z$ in the linear model

$$y = d\beta + Z\alpha + \varepsilon, \qquad d = Z\gamma + v,$$

where $\alpha_j \ne 0$ means instrument $j$ is **invalid** (a direct, pleiotropic effect on $y$). Let $A = \{j : \alpha_j \ne 0\}$ with $|A| = s$, and let $\Gamma = \gamma\beta + \alpha$ be the reduced-form coefficients, so the per-instrument ratios are

$$\pi_j = \frac{\Gamma_j}{\gamma_j} = \beta + \frac{\alpha_j}{\gamma_j}.$$

$\beta$ is identified when the valid instruments form the largest group of equal $\pi_j$; a sufficient condition is $s < L/2$. The Lasso approach (sisVIVE) estimates $\alpha$ by $\ell_1$-penalized regression of $y$ on $Z$ after projecting out $\hat d = Z\hat\gamma$.

**Selection failure of the Lasso.** Consistent selection by the Lasso requires an irrepresentable condition $\|C_{21}C_{11}^{-1}\operatorname{sign}(\alpha_1)\|_\infty < 1$ on the limit $C$ of $n^{-1}\tilde Z^\top \tilde Z$, where $\tilde Z$ is $Z$ with $\hat d$ projected out. This depends on the instrument strengths as well as their correlations: if $|\gamma_1^\top \operatorname{sign}(\alpha_1)| > \|\gamma_2\|_1$ ($\gamma_1$, $\gamma_2$ the first-stage coefficients of the invalid and valid instruments), the condition fails. With equal-strength instruments the condition can fail for some sign configurations of $\alpha_1$ once $s > L/2$; for uncorrelated equal-strength instruments it holds for every configuration when $s < L/2$. With $s < L/2$ it can still fail when the instrument strengths differ (as in the condition above) or the instruments are correlated, so the Lasso can select the wrong instruments even when $\beta$ is identified.

**Theorem (median estimator).** If $s < L/2$, then $\hat\beta_m = \operatorname{median}(\hat\pi_1,\dots,\hat\pi_L)$ is consistent for $\beta$, and $\sqrt n(\hat\beta_m - \beta)$ converges to an order statistic of the limiting normal distribution of the valid instruments' $\sqrt n(\hat\pi_j - \beta)$, generally with a nonzero asymptotic bias.

**Proposition (adaptive Lasso).** With weights $w_j = |\hat\alpha_{m,j}|^{-\nu}$ built from the median-based estimates $\hat\alpha_m = \hat\Gamma - \hat\gamma\hat\beta_m$, and a tuning parameter $\lambda_n = o(\sqrt n)$ with $n^{(\nu-1)/2}\lambda_n \to \infty$, the adaptive Lasso selects $A$ with probability tending to one, and $\sqrt n(\hat\alpha_{ad,A} - \alpha_A)$ is asymptotically normal. Consequently $\sqrt n(\hat\beta_{ad} - \beta) \to N(0, \sigma^2_{\beta,\mathrm{or}})$, the limit of the oracle two-stage least squares estimator that knows which instruments are invalid.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

The median is robust because, when fewer than half the ratios $\pi_j$ are shifted away from $\beta$ by pleiotropy, the middle order statistic is a valid ratio in the limit; but its $\sqrt n$ limit is a biased order statistic, so it serves only as a consistent pilot. Adaptive weights inflate the penalty on instruments whose pilot $\hat\alpha_{m,j}$ is near zero and shrink it on clearly invalid ones, restoring oracle selection without any irrepresentable condition. The methods are illustrated on a UK Biobank Mendelian randomization study of the effect of body mass index on diastolic blood pressure with 96 SNPs as candidate instruments.

## Sources

- F. Windmeijer, H. Farbmacher, N. Davies and G. Davey Smith, "On the use of the Lasso for instrumental variables estimation with some invalid instruments", Journal of the American Statistical Association 114 (2019), Eqs. (3)–(9), Propositions 1–3, Corollaries 1–2 and Theorem 1, <https://doi.org/10.1080/01621459.2018.1498346>, PMCID: PMC6817329.
