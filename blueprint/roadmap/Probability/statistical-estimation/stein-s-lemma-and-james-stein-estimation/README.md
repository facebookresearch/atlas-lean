# Stein's lemma and James–Stein estimation

For $X \sim \mathcal N(\mu, \sigma^2)$, Gaussian integration by parts gives Stein's identity $\mathbb E[(X - \mu) g(X)] = \sigma^2\, \mathbb E[g'(X)]$. Applied coordinatewise to $X \sim \mathcal N_p(\theta, I)$ it yields Stein's unbiased risk estimate (SURE) for any estimator $X + g(X)$, and SURE applied to $g(x) = -(p - 2) x / \|x\|^2$ gives the risk of the James–Stein estimator, $p - (p - 2)^2\, \mathbb E\|X\|^{-2}$, strictly below the risk $p$ of $X$ when $p \ge 3$. Shrinking towards the grand mean instead of $0$ costs one dimension: that estimator dominates $X$ when $N \ge 4$ (Efron 2021, Theorem 1, which credits James and Stein 1961). Efron and Morris read the James–Stein estimator as an empirical Bayes rule: under the prior $\theta_i \sim \mathcal N(0, A)$ the Bayes rule shrinks $X$ by $1 - 1/V$ with $V = A + 1$, and $(p - 2)/\|X\|^2$ is an unbiased estimate of $1/V$.

- [Stein's lemma](integrable-and-integral-sub-mul-gaussian.md)
- [Stein's lemma, coordinate form](integral-sub-mul-pi-gaussian-real.md)
- [Quadratic risk of the usual Gaussian mean estimator](integral-sum-sq-sub-pi-gaussian-real.md)
- [Stein's unbiased risk estimate](integral-sum-sq-add-sub-pi-gaussian-real.md)
- [James–Stein estimator](james-stein.md)
- [Risk of the James–Stein estimator](integrable-and-integral-james-stein-risk.md)
- [James–Stein dominance](integral-james-stein-risk-lt.md)
- [Mean of the inverse squared norm of a standard Gaussian vector](integral-inv-sum-sq-pi-gaussian-real-zer.md)
- [The James–Stein shrinkage factor estimates $1/V$ without bias](integral-james-stein-factor-pi-gaussian.md)

## Shrinkage towards the grand mean and the positive-part estimator

- [James–Stein estimator shrinking towards the grand mean](james-stein-grand-mean.md)
- [James–Stein shrinkage towards the grand mean dominates the MLE](integral-james-stein-grand-mean-risk-lt.md)
- [Positive-part James–Stein estimator](james-stein-plus.md)
- [The positive-part James–Stein estimator is at least as good as James–Stein](integral-james-stein-plus-risk-le.md)

## Related topics

- [Empirical Bayes and Tweedie's formula](../../bayesian-statistics/empirical-bayes-and-tweedie-s-formula/README.md): the Bayes rule that the James–Stein estimator imitates, and Tweedie's formula for general priors.
- [Lande's selection gradient](../../../Biology/quantitative-genetics/lande-s-selection-gradient/README.md): Stein's lemma in quantitative genetics, where it turns the covariance of trait and fitness into the mean fitness gradient.
- [Bootstrap and the Mallows metric](../bootstrap-and-the-mallows-metric/README.md): Efron's other approach to frequentist accuracy; the results above do not depend on it.
