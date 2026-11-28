# Unbiasedness of the residual variance estimator

Let $X$ be a real $m \times k$ matrix with $X^\top X$ invertible and $k < m$, and let $\varepsilon$ be a random vector in $\mathbb{R}^m$ on a probability space with square-integrable, mean-zero coordinates and $\operatorname{Cov}(\varepsilon_i, \varepsilon_j) = \sigma^2\mathbf 1[i = j]$. For every $\beta \in \mathbb{R}^k$, with $y = X\beta + \varepsilon$ and $\hat\beta = (X^\top X)^{-1}X^\top y$,

$$\mathbb{E}\Big[\frac{\|y - X\hat\beta\|^2}{m - k}\Big] = \sigma^2.$$

No Gaussian assumption is made.
