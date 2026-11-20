# Contrast t statistic

For an $n \times p$ design matrix $X$, a contrast $a$, a hypothesized value $\beta$ and observations $y$,
the $t$ statistic for testing the value $a^\top \beta$ is
$$T = \frac{a^\top (\hat\beta - \beta)}{\sqrt{\dfrac{\|y - X\hat\beta\|^2}{n - p} \, a^\top (X^\top X)^{-1} a}},$$
where $\hat\beta$ is the least-squares estimate from $y$. When $p \ge n$, when $X^\top X$ is singular, or
when the denominator vanishes, $T$ is taken to be $0$.
