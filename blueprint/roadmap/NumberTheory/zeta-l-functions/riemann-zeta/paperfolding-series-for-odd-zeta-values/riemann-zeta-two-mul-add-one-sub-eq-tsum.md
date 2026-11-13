# Tóth's paperfolding and Thue–Morse series for $\zeta(2k+1)$

Let $(f_n)_{n \ge 0}$ be the
regular paperfolding sequence and $(t_n)_{n \ge 0}$ the Thue–Morse sequence, both indexed from
$0$, and let $E_{2k}$ be the even-index Euler number. For every integer $k \ge 1$,

$$
\zeta(2k+1) - \frac{2^{2k-1} |E_{2k}| \pi^{2k+1}}{(2k)!} =
\sum_{n \ge 0} \frac{N_k(n)}{(n+1)^{2k+1}},
$$

where

$$
N_k(n) = (2^{4k+1} - 2^{2k})(2 f_n - 1) +
2^{-(2k+1)} \bigl((2^{2k+1} + 1) t_n + (2^{2k+1} - 1) t_{n+1}\bigr).
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$ (so $b_{2n} = b_n$, $b_{4n+1} = 0$ and
$b_{4n+3} = 1$), the right side is $\sum_{n \ge 1} N(n;k)/n^{2k+1}$ with
$N(n;k) = (2^{4k+1} - 2^{2k})(2b_n - 1) +
2^{-(2k+1)}((2^{2k+1} + 1) t_{n-1} + (2^{2k+1} - 1) t_n)$.

## Sources

- László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Theorem 2 (`jis-2025-25.4.4-thm-2`); `bₙ`, `tₙ` read from arXiv:2508.04151v1.
