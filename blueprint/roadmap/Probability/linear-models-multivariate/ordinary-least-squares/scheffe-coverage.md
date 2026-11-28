# Scheffé simultaneous confidence set by inverting the F test

Let $X$ be a real $m \times k$ design matrix with $X^\top X$ invertible and $k < m$, and consider the linear model $y = X\beta + \varepsilon$ with $\beta \in \mathbb{R}^k$ and a random error vector $\varepsilon$ in $\mathbb{R}^m$ on a probability space. Write $\hat\beta(y) = (X^\top X)^{-1} X^\top y$ for the ordinary least-squares estimator. Suppose $\sigma > 0$ and $\sigma^{-1}\varepsilon$ is a standard Gaussian vector (independent standard normal coordinates). Let $C$ be a real $r \times k$ matrix with $r > 0$ and $C(X^\top X)^{-1}C^\top$ invertible, $\alpha \in [0, 1]$, and $c$ with $P(0 \le F_{r, m-k} \le c) \ge 1 - \alpha$ for $F_{r,m-k}$ with Snedecor's $F$ law. For $t \in \mathbb{R}^r$ let $F_t(y)$ be the $F$ statistic of the hypothesis $C\beta = t$. Then with $y = X\beta + \varepsilon$

$$P\big(F_{C\beta}(y) \le c\big) \ge 1 - \alpha:$$

the confidence set $\{t : F_t(y) \le c\}$ for $C\beta$, obtained by inverting the $F$ tests, has coverage at least $1 - \alpha$.
