# A biased variance estimator with smaller mean squared error

Let $n \ge 2$ and let $X_1,\dots,X_n$ be independent draws from the normal law $N(\mu,v)$ of mean $\mu$ and variance $v>0$. Write $\bar X$ for the sample mean and $Q=\sum_i (X_i-\bar X)^2$. Both variance estimators are square-integrable. The usual estimator $S^2=Q/(n-1)$ is unbiased and has mean squared error $2v^2/(n-1)$; the estimator $\hat v=Q/n$ has bias $-v/n$ and mean squared error $(2n-1)v^2/n^2$, which is strictly smaller.

To see this, fit an intercept-only model; its residuals are the deviations from the sample mean. The normalized residual sum of squares $Q/v$ has the chi-square law with $k=n-1$ degrees of freedom, the gamma law of shape $k/2$ and rate $1/2$. Its mean is $k$ and its variance is $2k$, so $E[Q]=(n-1)v$ and $\operatorname{Var}(Q)=2(n-1)v^2$. The bias–variance decomposition gives the two errors: $\operatorname{Var}(Q)/(n-1)^2$ and $\operatorname{Var}(Q)/n^2+(v/n)^2$, respectively. The second is smaller because $(2n-1)(n-1)=2n^2-3n+1<2n^2$.

## Sources

- The comparison is derived here from the Gaussian residual law, gamma moments, and the bias–variance decomposition.
