# Exact F confidence region for linear combinations of coefficients

Let $X$ be a real $m \times k$ design matrix with $X^\top X$ invertible and $k < m$, and consider the linear model $y = X\beta + \varepsilon$ with $\beta \in \mathbb{R}^k$ and a random error vector $\varepsilon$ in $\mathbb{R}^m$ on a probability space. Write $\hat\beta(y) = (X^\top X)^{-1} X^\top y$ for the ordinary least-squares estimator. Suppose $\sigma > 0$ and $\sigma^{-1}\varepsilon$ is a standard Gaussian vector (independent standard normal coordinates). Let $C$ be a real $r \times k$ matrix with $r \ge 1$ and $C(X^\top X)^{-1}C^\top$ invertible, and for $\gamma \in \mathbb{R}^r$ let $F_\gamma(y)$ be the $F$ statistic of the hypothesis $C\beta = \gamma$. Write $G$ for the distribution function and $q$ for the quantile function of Snedecor's $F$ law with $(r, m - k)$ degrees of freedom. For every $\beta$ and $\alpha \in (0, 1)$, the region $\{\gamma : F_\gamma(y) \le q(1 - \alpha)\}$, $y = X\beta + \varepsilon$, contains $C\beta$ with probability exactly $1 - \alpha$.

## Sources

- G. A. F. Seber and A. J. Lee, *Linear Regression Analysis*, 2nd ed., Wiley (2003), Chapters 4 and 5.
