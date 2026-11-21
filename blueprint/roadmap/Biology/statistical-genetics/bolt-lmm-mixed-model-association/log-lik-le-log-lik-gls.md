# GLS maximizes the marginal likelihood

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix of full column rank ($X\beta = 0$ only for $\beta = 0$), and let $y \in \mathbb{R}^n$. Then for every $\beta \in \mathbb{R}^p$,

$$\ell(X\beta) \le \ell(X\hat\beta),$$

where $\ell$ is the [marginal log-likelihood](log-lik.md) and $\hat\beta$ the [generalized least-squares estimator](gls.md).
