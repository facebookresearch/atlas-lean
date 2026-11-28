# Total variance of a bootstrap row

For real data $x_0, x_1, \dots$ let $\bar x_n = \frac1n\sum_{i<n}x_i$, and let the bootstrap coupling be the probability measure on arrays $(\omega_{n,k})$ with independent entries, $\omega_{n,k}$ having the empirical law of $x_0, \dots, x_{\max(n,1)-1}$; write $Y_{n,k} = (\omega_{n,k} - \bar x_n)/\sqrt n$ for the bootstrap triangular array. Then $\sum_{k<n}\mathbb{E}[Y_{n,k}^2] = \frac1n\sum_{i<n}(x_i - \bar x_n)^2$ for every $n$ (both $0$ for $n = 0$).
