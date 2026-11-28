# Central limit theorem for bootstrap rows

For real data $x_0, x_1, \dots$ let $\bar x_n = \frac1n\sum_{i<n}x_i$, and let the bootstrap coupling be the probability measure on arrays $(\omega_{n,k})$ with independent entries, $\omega_{n,k}$ having the empirical law of $x_0, \dots, x_{\max(n,1)-1}$; write $Y_{n,k} = (\omega_{n,k} - \bar x_n)/\sqrt n$ for the bootstrap triangular array. If $\sum_{k<n}\mathbb{E}[Y_{n,k}^2] \to v \ge 0$ and the array satisfies the Lindeberg condition, then $\sum_{k<n}Y_{n,k}$ converges in distribution to $\mathcal N(0, v)$ (the point mass at $0$ when $v = 0$).
