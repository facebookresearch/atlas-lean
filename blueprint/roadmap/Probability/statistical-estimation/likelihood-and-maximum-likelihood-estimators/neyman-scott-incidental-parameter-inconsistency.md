# Neyman–Scott inconsistency for groups of any size

For pairs of observations ($T = 2$) the [inconsistency of the maximum-likelihood variance](../../not-yet-classified/part-17/neyman-scott/mle-variance-inconsistent.md) and the [consistency of the conditional estimate](../../not-yet-classified/part-17/neyman-scott/conditional-variance-consistent.md) are stated separately. This page states the general case. Let $y_{it} = \alpha_i + u_{it}$, $t = 1, \dots, T$, $i = 1, \dots, n$, with an integer $T \ge 2$, $u_{it}$ i.i.d. $N(0, \sigma^2)$ with $\sigma^2 > 0$, and one incidental mean $\alpha_i$ per group. The joint maximum-likelihood estimator of the structural parameter $\sigma^2$ is

$$\hat\sigma^2 = \frac{1}{nT} \sum_{i=1}^n \sum_{t=1}^T (y_{it} - \bar y_i)^2 \sim \frac{\sigma^2}{nT}\, \chi^2_{n(T-1)},$$

so $E\hat\sigma^2 = \sigma^2 (T - 1)/T$, and by the strong law of large numbers $\hat\sigma^2 \to \sigma^2 (T - 1)/T$ almost surely as $n \to \infty$ with $T$ fixed, whatever the $\alpha_i$ (Neyman and Scott 1948, in the form given by Koenker). The likelihood of the within-group deviations, equivalently the likelihood conditional on the sufficient statistics $\bar y_i$ for the $\alpha_i$, gives the consistent estimator $\frac{1}{n(T - 1)} \sum_{i,t} (y_{it} - \bar y_i)^2$.

## Depends on

- [Inconsistency of the maximum-likelihood variance](../../not-yet-classified/part-17/neyman-scott/mle-variance-inconsistent.md)

## Expansion

1. The model with one incidental mean per group.
2. The joint maximum-likelihood estimators and the law of $\hat\sigma^2$.
3. The almost-sure limit $\sigma^2(T - 1)/T$ by the strong law of large numbers.
4. The conditional (or marginal) likelihood and its consistent estimator.
5. Incidental variances $\sigma_i^2$ and the dynamic panel models of the source, as separate statements.

## Sources

- R. Koenker, Incidental parameters and dynamic bias in panel data, Lecture 18, Economics 536, University of Illinois, 2016.
- Original result: J. Neyman and E. L. Scott, Consistent estimates based on partially consistent observations, Econometrica 16 (1948), 1–32. <https://doi.org/10.2307/1914288> The inconsistency of the variance estimator follows Koenker's lecture notes.
