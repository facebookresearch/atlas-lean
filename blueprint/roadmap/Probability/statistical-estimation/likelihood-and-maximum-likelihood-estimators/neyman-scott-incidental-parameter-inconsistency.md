# Neyman–Scott inconsistency for groups of any size

For pairs of observations ($T = 2$) the [inconsistency of the maximum-likelihood variance](../../not-yet-classified/part-17/neyman-scott/mle-variance-inconsistent.md) and the [consistency of the conditional estimate](../../not-yet-classified/part-17/neyman-scott/conditional-variance-consistent.md) are stated separately. This page states the general case. Let $y_{it} = \alpha_i + u_{it}$, $t = 1, \dots, T$, $i = 1, \dots, n$, with an integer $T \ge 2$, $u_{it}$ i.i.d. $N(0, \sigma^2)$ with $\sigma^2 > 0$, and one incidental mean $\alpha_i$ per group. The joint maximum-likelihood estimator of the structural parameter $\sigma^2$ is

$$\hat\sigma^2 = \frac{1}{nT} \sum_{i=1}^n \sum_{t=1}^T (y_{it} - \bar y_i)^2 \sim \frac{\sigma^2}{nT}\, \chi^2_{n(T-1)},$$

so $E\hat\sigma^2 = \sigma^2 (T - 1)/T$, and by the strong law of large numbers, applied to the group residual sums of squares divided by $T$, which are i.i.d. whatever the $\alpha_i$, $\hat\sigma^2 \to \sigma^2 (T - 1)/T$ almost surely as $n \to \infty$ with $T$ fixed, whatever the $\alpha_i$ (Neyman and Scott 1948, Example 1; Lancaster 2000, Section 2). The likelihood of the within-group deviations, equivalently the likelihood conditional on the sufficient statistics $\bar y_i$ for the $\alpha_i$, gives the consistent estimator $\frac{1}{n(T - 1)} \sum_{i,t} (y_{it} - \bar y_i)^2$ (Lancaster 2000, Section 6.1, equation (7), with Section 5 for conditioning in general).

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)
- [Cochran's theorem, projection form](../../linear-models-multivariate/cochran-s-theorem/std-gaussian-map-norm-sq-star-projection.md)

## Expansion

1. The model with one incidental mean per group.
2. The joint maximum-likelihood estimators and the law of $\hat\sigma^2$, by the projection form of Cochran's theorem applied to the standardized errors projected off the group means.
3. The almost-sure limit $\sigma^2(T - 1)/T$ by the strong law of large numbers.
4. The conditional (or marginal) likelihood and its consistent estimator.
5. Neyman and Scott's examples with incidental variances $\sigma_i^2$, and the dynamic panel models surveyed by Lancaster (2000, Section 4), as separate statements.

## Sources

- Original result: J. Neyman and E. L. Scott, Consistent estimates based on partially consistent observations, Econometrica 16 (1948), 1–32, Example 1. <https://doi.org/10.2307/1914288>
- T. Lancaster, The incidental parameter problem since 1948, J. Econometrics 95 (2000), 391–413, Sections 2, 5 and 6.1. <https://doi.org/10.1016/S0304-4076(99)00044-5>
