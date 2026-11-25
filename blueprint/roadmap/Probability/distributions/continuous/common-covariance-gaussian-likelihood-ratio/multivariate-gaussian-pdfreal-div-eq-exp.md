# Multivariate Gaussian PDFReal div eq exp

Let $\iota$ be a finite index set and identify vectors in $\mathbb{R}^\iota$ with column vectors. For $s_1, s_0, y \in \mathbb{R}^\iota$ and a real $\iota \times \iota$ matrix $R$, write

$$\Lambda(y) = (s_1 - s_0)^{\mathsf T} R^{-1} y - \tfrac12 \bigl(s_1^{\mathsf T} R^{-1} s_1 - s_0^{\mathsf T} R^{-1} s_0\bigr)$$

for the common-covariance log-likelihood ratio statistic. If $R$ is positive definite, then for every $y \in \mathbb{R}^\iota$ the ratio of the Gaussian densities with means $s_1, s_0$ and common covariance $R$ is

$$\frac{\varphi_{s_1, R}(y)}{\varphi_{s_0, R}(y)} = \exp \Lambda(y), \qquad \varphi_{s, R}(y) = \frac{1}{(2\pi)^{\lvert\iota\rvert/2} \sqrt{\det R}} \exp\Bigl(-\tfrac12 (y - s)^{\mathsf T} R^{-1} (y - s)\Bigr).$$
