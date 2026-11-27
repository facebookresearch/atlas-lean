# A biased variance estimator with smaller mean squared error

Let $n \ge 2$ and $X_1, \dots, X_n$ be i.i.d. $N(\mu, v)$ with $v > 0$, let $\bar X$ be the sample mean and $Q = \sum_i (X_i - \bar X)^2$. The unbiased estimator $S^2 = Q/(n-1)$ of $v$ has mean squared error $2v^2/(n-1)$; the estimator $\hat v = Q/n$ has bias $-v/n$ and mean squared error $(2n-1)v^2/n^2$, which is strictly smaller. So unbiasedness does not minimize mean squared error.

Proof. $Q/v$ has the chi-square law with $k = n - 1$ degrees of freedom, which is the gamma law with shape $k/2$ and rate $1/2$; its mean is $(k/2)/(1/2) = k$ and its variance is $(k/2)/(1/2)^2 = 2k$, so $E[Q] = (n-1)v$ and $\operatorname{Var}(Q) = 2(n-1)v^2$. By the bias–variance decomposition, $\operatorname{MSE}(S^2) = \operatorname{Var}(Q)/(n-1)^2 = 2v^2/(n-1)$ and $\operatorname{MSE}(\hat v) = \operatorname{Var}(Q)/n^2 + (v/n)^2 = (2n-1)v^2/n^2$. Finally $(2n-1)(n-1) = 2n^2 - 3n + 1 < 2n^2$.

## Proof depends on

- [Bias–variance decomposition for a parametric family](family-mean-squared-error-eq-variance-ad.md): bias–variance decomposition.
- [Chi-squared law of the residual quadratic form](../../linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/has-law-dot-product-residual-matrix.md): chi-square law of the residual sum of squares, applied to the intercept-only design.
- [Chi-square distribution](../../distributions/continuous/chi-square-distribution/chi-square-measure.md): the chi-square law with $k$ degrees of freedom as the gamma law with shape $k/2$ and rate $1/2$.
- [Mean of the gamma law](../../distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md): mean of the gamma law.
- [Gamma law has finite second moment](../../distributions/continuous/gamma-distribution/gamma-moments/mem-lp-id-gamma-measure.md): finite second moment of the gamma law.
- [Variance of the gamma law](../../distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md): variance of the gamma law.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
