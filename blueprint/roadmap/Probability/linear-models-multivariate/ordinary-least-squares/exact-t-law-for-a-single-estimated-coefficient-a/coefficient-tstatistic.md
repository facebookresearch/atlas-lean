# t statistic of a single regression coefficient

Let $X$ be a real $n \times p$ design matrix (rows and columns indexed by finite sets of sizes $n$ and $p$) and $y \in \mathbb{R}^n$, and let $\hat\beta = (X^\top X)^{-1} X^\top y$ be the least-squares estimator, where the inverse of a singular matrix is taken to be the zero matrix. For a coordinate $j$ and a value $\beta \in \mathbb{R}^p$, the $t$ statistic of the $j$-th coefficient is

$$t_j = \frac{\hat\beta_j - \beta_j}{\sqrt{\dfrac{\|y - X\hat\beta\|^2}{n - p}\,\big[(X^\top X)^{-1}\big]_{jj}}},$$

where $n - p$ is truncated at $0$, a quotient by $0$ is $0$, and the square root of a negative number is $0$.
