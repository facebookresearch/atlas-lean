# Zurita's polynomial $T_{n-2}$

For a natural number $n$ and a real number $x$,
$T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$, where $t_0, t_1, \dots$ are the coefficients of
Zurita's polynomial $T_{n-2}$; for $n \le 1$ the sum is empty and $T_{n-2}(x) = 0$. For
$n \ge 2$ these coefficients are given by $t_{n-2} = -s_{n-1}/2 - c_n$ and
$t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for $k = n - 2, \dots, 1$, where
$s_0 = 1/(1/2 - n)$ and $s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for $k \ge 1$ are the
coefficients of Zurita's polynomial $S_n$, and $c_n = s_n/2 - 1$.

## Sources

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2.
