# Pointwise form of the t statistic

In the linear model $y = X\beta + e$ with an $n \times p$ design matrix $X$, for every error vector $e$,
every $\sigma > 0$ and every contrast $a$ with $q = a^\top (X^\top X)^{-1} a \ge 0$, the $t$ statistic for
testing the value $a^\top \beta$ is $T = U / \sqrt{V / d}$, where
$U = a^\top (\hat\beta - \beta) / (\sigma \sqrt q)$ is the standardized contrast,
$V = \|y - X\hat\beta\|^2 / \sigma^2$, and $d = n - p$. Here $d$ is taken to be $0$ when $p > n$, the
inverse of a singular matrix is taken to be $0$, and a ratio with denominator $0$ is taken to be $0$, so
both sides are $0$ when $q = 0$, $V = 0$ or $p \ge n$.
