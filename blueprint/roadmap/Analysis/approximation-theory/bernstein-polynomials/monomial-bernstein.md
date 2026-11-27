# Monomials in the Bernstein basis

For integers $0 \le \nu \le n$, the Bernstein polynomial is $b_{n,\nu}(s) = \binom{n}{\nu} s^{\nu} (1 - s)^{n - \nu}$, a real polynomial in $s$. For integers $0 \le k \le n$ and every real number $s$,

$$s^k = \sum_{\nu=0}^{n} \frac{\binom{\nu}{k}}{\binom{n}{k}}\, b_{n,\nu}(s),$$

where $\binom{\nu}{k} = 0$ for $\nu < k$. This includes $k = 0$, $n = 0$ and the endpoints $s = 0$ and $s = 1$.
