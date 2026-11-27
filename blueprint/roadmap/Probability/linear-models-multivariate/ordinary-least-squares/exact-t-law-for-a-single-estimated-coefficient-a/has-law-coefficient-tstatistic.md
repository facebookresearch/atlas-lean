# Exact t law of a single estimated coefficient

Let $X$ be a real $n \times p$ design matrix with $X^\top X$ invertible and $p < n$, let $\beta \in \mathbb{R}^p$ and $\sigma > 0$, and let $y = X\beta + \varepsilon$ where the standardized errors $\sigma^{-1}\varepsilon$ have independent standard normal coordinates. For every coordinate $j$, the statistic

$$t_j = \frac{\hat\beta_j - \beta_j}{\sqrt{\dfrac{\|y - X\hat\beta\|^2}{n - p}\,\big[(X^\top X)^{-1}\big]_{jj}}}, \qquad \hat\beta = (X^\top X)^{-1} X^\top y,$$

has Student's $t$ law with $n - p$ degrees of freedom, the law of $Z / \sqrt{V/(n-p)}$ for independent $Z \sim N(0,1)$ and $V \sim \chi^2_{n-p}$.
