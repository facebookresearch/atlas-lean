# The $n^{\log_2 3}$ bound for the Karatsuba cost recurrence

Let $T$ be the Karatsuba cost
recurrence, $T(n) = 1$ for $n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$. For
every natural number $n \ge 1$, $T(n) \le 9\, n^{\log_2 3}$.
