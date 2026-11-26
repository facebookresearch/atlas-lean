# Power-weighted sums of a sequence via its hypersequences

Let $a$ be a sequence of complex
numbers, let $a^{(r)}_n$ denote its hypersequence of generation $r$, let
$p_{\ell,m}(x, y) = \sum_{i=0}^{m} (-1)^i \binom{m}{i} (ix + y)^\ell$ be the alternating binomial
power sum, and let $S(j, m)$ denote the Stirling numbers of the second kind. Then for all
natural numbers $\ell$ and $n$, with the convention $0^0 = 1$,

$$\sum_{k=0}^{n} k^\ell a_k = \sum_{m=0}^{\ell} p_{\ell,m}(1, n + 1)\, a^{(m+1)}_n$$

and

$$\sum_{k=0}^{n} k^\ell a_k = \sum_{j=0}^{\ell} \binom{\ell}{j}
\Bigl(\sum_{m=0}^{j} (-1)^m\, m!\, S(j, m)\, a^{(m+1)}_n\Bigr) (n + 1)^{\ell-j}.$$

This is the case $r = 0$ of the corresponding identity for $\sum_{k=0}^{n} k^\ell a^{(r)}_k$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Corollary 3.
