# Piecewise formula for the 2-adic valuation of $H_n - H_{n-m}$

Let
$H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th harmonic number and let $\nu_2$ denote the $2$-adic
valuation on the rational numbers (for a positive integer it is the exponent of $2$ in its
factorization). Let $m$ and $n$ be natural numbers with $1 \le m \le n$, and put
$M = \lceil \log_2(m + 1) \rceil$ and $j = \lfloor (n - m) / 2^M \rfloor$. If
$2^M j + m \le n \le 2^M (j + 1) - 1$, then $\nu_2(H_n - H_{n-m}) = 1 - M$. If
$2^M (j + 1) \le n \le 2^M (j + 1) + m - 1$, then $\nu_2(H_n - H_{n-m}) = -M - \nu_2(j + 1)$.

## Sources

- Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024), Article A27, Theorem 6, formula (3.1): let `M = ⌈log₂(m + 1)⌉` and `j = ⌊(n - m) / 2^M⌋`, where `1 ≤ m ≤ n`. Then `ν₂(H_n - H_{n-m}) = -M + 1` when `2^M * j + m ≤ n ≤ 2^M * (j + 1) - 1`, and `ν₂(H_n - H_{n-m}) = -M - ν₂(j + 1)` when `2^M * (j + 1) ≤ n ≤ 2^M * (j + 1) + m - 1`.
