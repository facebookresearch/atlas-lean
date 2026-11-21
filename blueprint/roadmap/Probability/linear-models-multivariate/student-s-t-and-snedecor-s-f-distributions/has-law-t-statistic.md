# Exact t law of a contrast

In the linear model $y = X\beta + \varepsilon$ with an $n \times p$ design $X$, $X^\top X$ invertible,
$p < n$, $\sigma > 0$, $\varepsilon / \sigma$ a standard Gaussian vector, and a nonzero contrast $a$, the
statistic
$$T = \frac{a^\top (\hat\beta - \beta)}{\sqrt{\dfrac{\|y - X\hat\beta\|^2}{n - p} \, a^\top (X^\top X)^{-1} a}}$$
has Student's $t$ law with $n - p$ degrees of freedom.
