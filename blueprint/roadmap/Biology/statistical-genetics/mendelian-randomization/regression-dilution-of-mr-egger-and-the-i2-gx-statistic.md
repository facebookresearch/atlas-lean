# Regression dilution of MR-Egger and the $I^2_{GX}$ statistic

Two-sample summary data for $L$ uncorrelated variants consist of SNP–exposure estimates $\hat\gamma_j$ and SNP–outcome estimates $\hat\Gamma_j$ from non-overlapping samples, with

$$\hat\gamma_j \sim N(\gamma_j, \sigma_{Xj}^2), \qquad \hat\Gamma_j \sim N(\alpha_j + \beta\gamma_j, \sigma_{Yj}^2),$$

where $\beta$ is the causal effect, $\alpha_j$ the pleiotropic effect of variant $j$, and all $\gamma_j > 0$ after allele orientation. The **NOME** (no measurement error) assumption treats $\hat\gamma_j = \gamma_j$, i.e. $\sigma_{Xj}^2 = 0$.

**Dilution of the slope.** Under InSIDE (pleiotropic effects independent of instrument strengths) but with NOME violated, the [MR-Egger slope](egger-slope.md) (unweighted, for simplicity) has, approximately,

$$\mathbb E[\hat\beta_{1E}] \approx \beta\,\frac{\operatorname{Var}(\gamma)}{\operatorname{Var}(\hat\gamma)} = \beta\,\frac{\sigma_\gamma^2}{\sigma_\gamma^2 + s^2},$$

where $\sigma_\gamma^2$ is the spread of the true $\gamma_j$ and $s^2$ the average extra variance from estimation error. The slope is attenuated towards zero. Because the Egger slope and intercept estimates are negatively correlated, the intercept is then biased, which inflates the type I error of the MR-Egger test for directional pleiotropy when $\beta > 0$ and pleiotropy is balanced.

**The $I^2_{GX}$ statistic.** With $\bar{\hat\gamma}$ the $1/\sigma_{Xj}^2$-weighted mean of the $\hat\gamma_j$, define

$$Q_{GX} = \sum_{j=1}^{L}\frac{(\hat\gamma_j - \bar{\hat\gamma})^2}{\sigma_{Xj}^2}, \qquad I^2_{GX} = \frac{Q_{GX} - (L-1)}{Q_{GX}}.$$

Then $I^2_{GX}$ estimates the dilution factor $\sigma_\gamma^2/(\sigma_\gamma^2 + s^2)$, so on average $\hat\beta_{1E} \approx \beta I^2_{GX}$. A value $I^2_{GX} = 0.9$ means an expected relative bias of about $10\%$ towards the null. The paper presents this threshold as playing the role that $F = 10$ plays in conventional instrumental-variable analysis. Large individual $F$-statistics $F_j \approx \hat\gamma_j^2/\sigma_{Xj}^2$ do not guarantee a large $I^2_{GX}$: if the true $\gamma_j$ are similar in size, the dilution can still be severe. The weighted MR-Egger analysis uses a slightly adapted $I^2_{GX}$, given in the paper's appendix.

## Depends on

- [MR-Egger slope](egger-slope.md)
- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

MR-Egger is a regression of $\hat\Gamma_j$ on $\hat\gamma_j$ with an intercept. Measurement error in the regressor that is independent of the true $\gamma_j$ gives the classical errors-in-variables attenuation: the slope converges to $\beta$ times the reliability ratio $\operatorname{Var}(\gamma)/\operatorname{Var}(\hat\gamma)$. $Q_{GX}$ is Cochran's heterogeneity statistic for the $\hat\gamma_j$, viewed as a meta-analysis. Its expectation under homogeneity is $L - 1$, so $I^2_{GX}$ estimates the share of the observed spread of $\hat\gamma_j$ that is real heterogeneity rather than noise, which is the reliability ratio. Under the null $\beta = 0$ there is nothing to attenuate, so NOME violation does not bias the slope then. The IVW estimate, a regression through the origin, is affected instead by ordinary weak-instrument attenuation, governed by the $F_j$.

## Sources

- J. Bowden, F. Del Greco M, C. Minelli, G. Davey Smith, N. A. Sheehan and J. R. Thompson, "Assessing the suitability of summary data for two-sample Mendelian randomization analyses using MR-Egger regression: the role of the I² statistic", *International Journal of Epidemiology* 45(6) (2016), 1961–1974, <https://doi.org/10.1093/ije/dyw220> (PMC5446088), Methods (Equations 1–3 and section "Assessing regression dilution with $I^2_{GX}$") and Figure 2.
