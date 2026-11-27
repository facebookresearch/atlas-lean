# Karatsuba cost at powers of two

Let $T$ be the Karatsuba cost recurrence, $T(n) = 1$ for
$n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$. For every natural number $k$,
$T(2^k) + 2^{k+1} = 3^{k+1}$.

So at $n = 2^k$ digits the cost is exactly $3^{k+1} - 2^{k+1} = 3\, n^{\log_2 3} - 2n$.
