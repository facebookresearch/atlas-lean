# Bernoulli numbers via forward differences at $1$

Let $n$ and $r$ be positive integers
with $n \ge r + 1$, let $B_n$ be the $n$-th Bernoulli number, let $S(a, b)$ denote the Stirling
numbers of the second kind and let $\Delta^k 1^m$ be the $k$-th forward difference of
$y \mapsto y^m$ at $1$. For $k \ge 0$ write
$e_k = \sum_{j=0}^{r} (-1)^{k+j+r} \, 2^{r-j} \, \frac{(k+j)!}{k!} \, S(r, j)$. Then
$(-1)^n B_n = \frac{n}{2^n - 1} \sum_{k=0}^{n-1-r} e_k \, \frac{\Delta^k 1^{n-1-r}}{2^{k+1+r}}$.

## Sources

- Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli and Genocchi Numbers", Corollary 2.
