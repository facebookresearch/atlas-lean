# Exact coverage of the two-sample t interval at every threshold

Let $m, n \ge 1$ with $m + n \ge 3$, $\mu_1, \mu_2 \in \mathbb{R}$ and $v > 0$, and let $X_1, \dots, X_m$ i.i.d. $\mathcal N(\mu_1, v)$ and $Y_1, \dots, Y_n$ i.i.d. $\mathcal N(\mu_2, v)$ be independent samples on a probability space. Write $\bar X, \bar Y$ for the sample means, $S_p^2 = \big(\sum_i(X_i - \bar X)^2 + \sum_j(Y_j - \bar Y)^2\big)/(m + n - 2)$ for the pooled variance, and $t_{m+n-2}$ for Student's $t$ law with $m + n - 2$ degrees of freedom. Then for every $c \in \mathbb{R}$

$$P\Big(|\bar X - \bar Y - (\mu_1 - \mu_2)| \le c\sqrt{S_p^2(1/m + 1/n)}\Big) = t_{m+n-2}([-c, c]).$$
