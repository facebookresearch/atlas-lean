# Rn Deriv multivariate Gaussian common covariance ae reference

Let $\iota$ be a finite index set and identify vectors in $\mathbb{R}^\iota$ with column vectors. Write $N(s, R)$ for the multivariate Gaussian law on $\mathbb{R}^\iota$ with mean $s$ and covariance $R$. For $s_1, s_0, y \in \mathbb{R}^\iota$ and a real $\iota \times \iota$ matrix $R$, write

$$\Lambda(y) = (s_1 - s_0)^{\mathsf T} R^{-1} y - \tfrac12 \bigl(s_1^{\mathsf T} R^{-1} s_1 - s_0^{\mathsf T} R^{-1} s_0\bigr)$$

for the common-covariance log-likelihood ratio statistic. If $R$ is positive definite, then for $N(s_0, R)$-almost every $y \in \mathbb{R}^\iota$,

$$\frac{dN(s_1, R)}{dN(s_0, R)}(y) = \exp \Lambda(y).$$
