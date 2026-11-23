# The GLS maximizer is unique

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix of full column rank, and let $y \in \mathbb{R}^n$. Then for every $\beta \in \mathbb{R}^p$,

$$\ell(X\beta) = \ell(X\hat\beta) \iff \beta = \hat\beta,$$

where $\ell$ is the [marginal log-likelihood](log-lik.md) and $\hat\beta$ the [generalized least-squares estimator](gls.md).
