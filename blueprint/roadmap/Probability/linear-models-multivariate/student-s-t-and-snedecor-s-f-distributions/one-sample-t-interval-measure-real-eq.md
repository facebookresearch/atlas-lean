# Exact coverage of the two-sided one-sample t interval

Let $n \ge 2$, $\mu \in \mathbb{R}$ and $v > 0$, and let $X_1, \dots, X_n$ be i.i.d. $\mathcal N(\mu, v)$ on a probability space. Write $\bar X = \frac1n\sum_i X_i$, $S = \sqrt{\frac{1}{n-1}\sum_i(X_i - \bar X)^2}$, and $t_{n-1}$ for Student's $t$ law with $n - 1$ degrees of freedom. Then for every $c \in \mathbb{R}$

$$P\Big(|\bar X - \mu| \le \frac{cS}{\sqrt n}\Big) = t_{n-1}([-c, c]).$$

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.
