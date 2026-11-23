# Maximal marginal log-likelihood

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, let $X$ be a real $n \times p$ matrix of full column rank, and let $y \in \mathbb{R}^n$. Then

$$\ell(X\hat\beta) = -\frac{1}{2}\bigl(n \log(2\pi) + \log \det V + y^\top P y\bigr),$$

where $\ell$ is the [marginal log-likelihood](log-lik.md), $\hat\beta$ the [generalized least-squares estimator](gls.md) and $P$ the [residual-forming matrix](proj.md).
