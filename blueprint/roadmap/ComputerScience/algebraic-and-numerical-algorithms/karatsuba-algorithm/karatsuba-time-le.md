# Power-of-three bound on the cost of Karatsuba multiplication

Let $\ell(n)$ be the least
natural number $k$ with $n \le 2^k$ (so $\ell(n) = \lceil \log_2 n \rceil$ for $n \ge 1$). For all
natural numbers $B$, $n$, $x$ and $y$, the cost of Karatsuba multiplication of $x$ and $y$ as
$n$-digit numbers in base $B$ is at most $3^{\ell(n) + 1}$.
