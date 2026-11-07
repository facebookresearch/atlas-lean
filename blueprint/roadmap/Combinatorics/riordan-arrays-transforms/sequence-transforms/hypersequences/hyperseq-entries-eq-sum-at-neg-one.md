# Parisse's coefficients at $n$ from their values at $-1$

Let $n \in \mathbb{Z}$. For
$j, k \in \mathbb{N}$ let $e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, let $b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$
for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, with
$0^0 = 1$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$. Then
$e_{j,k}(n) = \sum_{i=0}^{k} \binom{j - k + i}{i} (n + 1)^i e_{j,k-i}(-1)$ for all $k \le j$,
$b_{j,k}(n) = \sum_{i=k}^{j} (-1)^{i-k} \binom{i}{k} (n + 1)^{i-k} b_{j,i}(-1)$ for all $j, k$,
and $c_{\ell,m}(n) = \sum_{i=m}^{\ell} \binom{\ell}{i} (n + 1)^{\ell-i} c_{i,m}(-1)$ for all
$\ell, m \in \mathbb{N}$.

The first identity is stated only for $k \le j$; for $k > j$ the source's upper index
$j - k + i$ of the binomial coefficient can be negative.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Proposition 3 (`integers-2026-A36-prop-3`).
