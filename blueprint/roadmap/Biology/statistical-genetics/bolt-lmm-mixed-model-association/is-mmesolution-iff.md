# Henderson's mixed-model equations give the GLS estimator and the BLUP

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with $K$ positive definite and $\sigma_g^2 > 0$, let $X$ be a real $n \times p$ matrix of full column rank, and let $y \in \mathbb{R}^n$, $\beta \in \mathbb{R}^p$, $g \in \mathbb{R}^n$. Then $(\beta, g)$ [solves Henderson's mixed-model equations](is-mmesolution.md) if and only if

$$\beta = \hat\beta \quad\text{and}\quad g = \sigma_g^2 K V^{-1} (y - X\hat\beta),$$

where $\hat\beta$ is the [generalized least-squares estimator](gls.md), $V$ the [phenotypic covariance](v.md), and the right-hand side of the second equation is the [BLUP](blup.md).
