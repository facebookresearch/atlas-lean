# Cost of Karatsuba multiplication

For all natural numbers $B$, $n$, $x$ and $y$, the cost
of Karatsuba multiplication of $x$ and $y$ as $n$-digit numbers in base $B$ equals $T(n)$, where
$T$ is the Karatsuba cost recurrence, $T(n) = 1$ for $n \le 1$ and
$T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$.

In particular the cost depends only on the digit count $n$, not on $B$, $x$ or $y$.
