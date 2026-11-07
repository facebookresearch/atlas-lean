# Alternating sum and recurrence for Arndt compositions

Let $a(n, m)$ be the number of
Arndt compositions of $n$ with $m$ parts, and write $K = n - m - \lfloor m/2 \rfloor$. For all
$n, m \ge 0$: if $m + \lfloor m/2 \rfloor \le n$, then

$$a(n, m) = \sum_{\ell=0}^{K} \binom{m+\ell-1}{\ell} \binom{n-m-\ell-1}{K-\ell} (-1)^{K-\ell},$$

and otherwise $a(n, m) = 0$. Moreover, for all $n \ge 3$ and $m \ge 2$,
$a(n, m) = a(n-1, m) + a(n-2, m) - a(n-3, m) + a(n-3, m-2)$. The binomial coefficients are the
generalized ones, $\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$ for an integer $r$, so the upper
index $-1$ is allowed and $\binom{-1}{k} = (-1)^k$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 2 (`integers-2024-A35-thm-2`).
