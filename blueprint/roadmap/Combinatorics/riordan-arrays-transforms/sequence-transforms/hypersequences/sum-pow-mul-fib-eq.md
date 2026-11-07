# Power-weighted sums of Fibonacci numbers

Let $F_k$ denote the Fibonacci numbers and let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum. Then for all natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,

$$\sum_{k=0}^{n} k^\ell F_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, F_{n+2(m+1)} -
\sum_{m=0}^{\ell} p_{\ell,m}(1, 1)\, F_{2(m+1)}.$$

The paper's conjecture on the constant term, stated after this theorem, is not included.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 10, Equation (4.7) (`integers-2024-A70-thm-10`).
