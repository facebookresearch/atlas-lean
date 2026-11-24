# Portfolio variance and diversification across uncorrelated assets

Let $n \ge 1$ and let $R_1, \dots, R_n$ be square-integrable returns with covariance matrix $\Sigma_{ij} = \operatorname{Cov}(R_i, R_j)$, so that a portfolio return $\sum_i w_iR_i$ has variance $w^{\mathsf T}\Sigma w$. If the returns are pairwise uncorrelated with $\operatorname{Var}(R_i) \le \sigma^2$, the equal-weight portfolio $w_i = 1/n$ has variance $\frac{1}{n^2}\sum_i \operatorname{Var}(R_i) \le \sigma^2/n$, which tends to $0$ as $n \to \infty$.

Proof. Expand the variance of the linear combination as the double sum of covariances; for uncorrelated returns only the diagonal terms remain.

## Proof depends on

- [Variance of a linear combination as a double sum of covariances](../../../../Biology/coalescent-theory/covariances-of-the-site-frequency-spectrum/variance-sum-eq-sum-covariance.md): variance of a linear combination as a double sum of covariances.
