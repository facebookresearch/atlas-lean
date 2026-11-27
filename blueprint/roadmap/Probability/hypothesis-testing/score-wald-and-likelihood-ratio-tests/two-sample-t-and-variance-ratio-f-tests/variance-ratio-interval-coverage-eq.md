# Exact confidence interval for a ratio of variances

Let $m, n \ge 2$, and let $X_1, \dots, X_m$ i.i.d. $\mathcal N(\mu_1, v_1)$ and $Y_1, \dots, Y_n$ i.i.d. $\mathcal N(\mu_2, v_2)$ be independent samples on a probability space with $v_1, v_2 > 0$. Write $S_X^2 = \sum_i(X_i - \bar X)^2/(m-1)$, $S_Y^2 = \sum_j(Y_j - \bar Y)^2/(n-1)$ and $R = S_X^2/S_Y^2$. For $\alpha \in (0, 1)$ and $q$ the quantile function of Snedecor's $F$ law with $(m - 1, n - 1)$ degrees of freedom,

$$P\Big(\frac{R}{q(1 - \alpha/2)} \le \frac{v_1}{v_2} \le \frac{R}{q(\alpha/2)}\Big) = 1 - \alpha.$$

## Sources

- E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005), §5.3.
