# Frobenius formula for binomial coefficients

For a natural number $n$, the integer $F(n) = \sum_{p \mid n} \Bigl(\sum_{d=1}^{v_p(n)} \binom{n}{p^d}\Bigr)(p - 1) - n$, where the outer sum runs over the prime factors $p$ of $n$ and $v_p(n)$ is the exponent of $p$ in $n$. The number $0$ is given no prime factors, so the sum is empty there and $F(0) = 0$; it is empty for $n = 1$ as well, and $F(1) = -1$.
