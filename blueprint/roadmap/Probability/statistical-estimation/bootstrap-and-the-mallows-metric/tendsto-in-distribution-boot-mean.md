# Conditional central limit theorem for the bootstrap mean

For real data $x_0, x_1, \dots$ write $\bar x_n = \frac1n\sum_{i<n}x_i$, $s^2_n = \frac1n\sum_{i<n}(x_i - \bar x_n)^2$, and under the bootstrap world of the data (independent draws $\omega_{n,k}$ from the empirical distribution of $x_0, \dots, x_{n-1}$) let $\bar x^*_n = \frac1n\sum_{k<n}\omega_{n,k}$ be the bootstrap mean. Suppose $s^2_n \to v \ge 0$ and the centred data satisfy the Lindeberg condition: for every $\varepsilon > 0$, $\frac1n\sum_{i<n}(x_i - \bar x_n)^2\mathbf 1\{|x_i - \bar x_n| > \varepsilon\sqrt n\} \to 0$. Then, under the bootstrap world, $\sqrt n\,(\bar x^*_n - \bar x_n)$ converges in distribution to $\mathcal N(0, v)$ (the point mass at $0$ when $v = 0$).

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Annals of Statistics* 9 (1981), 1196–1217.
