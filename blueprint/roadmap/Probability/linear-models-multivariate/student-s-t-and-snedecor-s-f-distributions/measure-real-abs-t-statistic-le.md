# Coverage identity for the contrast t statistic

In the linear model $y = X\beta + \varepsilon$ with an $n \times p$ design $X$, $X^\top X$ invertible,
$p < n$, $\sigma > 0$, $\varepsilon / \sigma$ a standard Gaussian vector, and a nonzero contrast $a$, the
contrast $t$ statistic $T$ satisfies, for every real $c$,
$$\Pr[|T| \le c] = t_{n-p}([-c, c]),$$
where $t_{n-p}$ is Student's $t$ law with $n - p$ degrees of freedom. Taking $c$ to be a $t_{n-p}$
quantile gives an exact confidence interval for $a^\top \beta$ (stated here without proof).
