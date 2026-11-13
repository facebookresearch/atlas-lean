# Power-weighted sums of Lucas numbers

Let $L_k$ denote the Lucas numbers, so $L_0 = 2$,
$L_1 = 1$ and $L_{k+2} = L_{k+1} + L_k$, and let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum. Then for all natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,

$$\sum_{k=0}^{n} k^\ell L_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, L_{n+2(m+1)} -
\sum_{m=0}^{\ell} p_{\ell,m}(1, 1)\, L_{2(m+1)} + L_0 \cdot 0^\ell.$$

The paper's conjecture on the constant term, stated after this theorem, is not included.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Theorem 11, Equation (4.9).
