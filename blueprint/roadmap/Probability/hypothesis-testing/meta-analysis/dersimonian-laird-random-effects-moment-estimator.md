# DerSimonian–Laird estimator of the between-study variance

In the random-effects model $y_i = \mu + \delta_i + e_i$, $i = 1, \dots, k$, with $k \ge 2$ studies, where $\delta_1, \dots, \delta_k, e_1, \dots, e_k$ are mutually independent, the $\delta_i$ have mean $0$ and variance $\Delta^2$, and the $e_i$ have mean $0$ and known sampling variances $s_i^2 > 0$, let $w_i = 1/s_i^2$, $\bar y_w = \sum_i w_i y_i/\sum_i w_i$ and Cochran's statistic $Q = \sum_i w_i (y_i - \bar y_w)^2$. DerSimonian and Laird (1986) equate $Q$ with its expected value to obtain the noniterative estimator

$$\hat\Delta^2 = \max\Bigl\{0,\ \frac{Q - (k - 1)}{\sum_i w_i - \sum_i w_i^2 / \sum_i w_i}\Bigr\},$$

and estimate $\mu$ by $\hat\mu = \sum_i w_i^* y_i/\sum_i w_i^*$ with $w_i^* = (w_i^{-1} + \hat\Delta^2)^{-1}$ and asymptotic standard error $(\sum_i w_i^*)^{-1/2}$. The moment equation is exact: from the first two moments alone, without normality,

$$E[Q] = (k - 1) + \Delta^2 \Bigl(S_1 - \frac{S_2}{S_1}\Bigr), \qquad S_r = \sum_i w_i^r,$$

since $E[Q] = \sum_i w_i \operatorname{Var}(y_i) - S_1 \operatorname{Var}(\bar y_w)$ with $\operatorname{Var}(y_i) = w_i^{-1} + \Delta^2$ and $\operatorname{Var}(\bar y_w) = (S_1 + \Delta^2 S_2)/S_1^2$. Since $k \ge 2$ and every $w_i > 0$, $S_1 - S_2/S_1 > 0$, so the untruncated estimator is well defined and unbiased for $\Delta^2$, and the truncation at $0$ biases $\hat\Delta^2$ upward.

## Depends on

- [Cochran's heterogeneity statistic Q](../../../Probability/hypothesis-testing/meta-analysis/cochran-q.md)
- [Cochran's Q is chi-square under homogeneity](../../../Probability/hypothesis-testing/meta-analysis/has-law-cochran-q.md)

## Expansion

1. The random-effects model and Cochran's $Q$ with known sampling variances.
2. The computation of $E[Q]$ from the first two moments.
3. The moment estimator, unbiasedness before truncation, and the upward bias of the truncated estimator.
4. The pooled estimator of $\mu$ and its variance when $\Delta^2$ is known; the plug-in version as a separate, approximate statement.
5. The equal-variance special case $\hat\Delta^2 = \max\{0, \sum_i (y_i - \bar y)^2/(k - 1) - \bar{s^2}\}$.

## Sources

- R. DerSimonian and N. Laird, Meta-analysis in clinical trials, Control. Clin. Trials 7 (1986), 177–188, section on the random-effects model, equations (3)–(4). <https://doi.org/10.1016/0197-2456(86)90046-2>
