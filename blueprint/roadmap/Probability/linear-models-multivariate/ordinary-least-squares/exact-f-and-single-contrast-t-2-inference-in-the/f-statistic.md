# F statistic for a linear hypothesis

Let $X$ be a real $m \times k$ design matrix, $C$ a real $r \times k$ matrix and $c \in \mathbb{R}^r$ (the hypothesis $C\beta = c$), and $\hat\beta(y) = (X^\top X)^{-1}X^\top y$. The $F$ statistic is

$$F(y) = \frac{(C\hat\beta(y) - c)^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1}(C\hat\beta(y) - c)\,/\,r}{\|y - X\hat\beta(y)\|^2\,/\,(m - k)},$$

with matrix inverses zero when singular, $x/0 = 0$, and truncated subtraction in $m - k$.
