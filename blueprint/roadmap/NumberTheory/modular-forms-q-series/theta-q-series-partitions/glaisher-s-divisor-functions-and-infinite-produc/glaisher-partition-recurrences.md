# Recurrences for partitions into even or distinct parts and for overpartitions

Let $n$
be a natural number. Let $p_e(m)$, $p_o(m)$ and $p_d(m)$ be the numbers of partitions of $m$
into even parts, into odd parts and into distinct parts, and let $\bar p(m)$ be the number of
overpartitions of $m$. For a positive integer $m$, write $\sigma(m)$ for the sum of the divisors
of $m$, $\sigma(m/2)$ for $\sigma$ evaluated at $m/2$ when $m$ is even and for $0$ when $m$ is
odd, $d_B(m)$ and $d_C(m)$ for the sums of the odd and of the even divisors of $m$, $d_D(m)$ for
the sum of the divisors $d$ of $m$ with $m/d$ odd, and $d_G(m) = \sum_{d \mid m} (-1)^{m/d-1} d$.
Then, with every sum running over $1 \le i \le n$,
$n\,p_e(n) = \sum_i d_C(i)\,p_e(n-i) = 2\sum_i \sigma(i/2)\,p_e(n-i)$,
$n\,p_d(n) = \sum_i d_B(i)\,p_o(n-i) = \sum_i d_G(i)\,p_d(n-i) =
\sum_i (\sigma(i) - 2\sigma(i/2))\,p_d(n-i)$, and
$n\,\bar p(n) = 2\sum_i d_D(i)\,\bar p(n-i) = 2\sum_i (\sigma(i) - \sigma(i/2))\,\bar p(n-i)$.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 10 (`jis-2024-24.1.6-thm-10`).
