# Recurrence, closed form and row sums of $e_{j,k}(n)$

Let $n \in \mathbb{N}$ and let
$e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in $n + 1, \dots, n + j$.
Write $[j, \ell]$ for the unsigned Stirling numbers of the first kind and
$x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the rising factorial. Then
$e_{0,k}(n) = \delta_{0,k}$ for all $k$;
$e_{j+1,k+1}(n) = e_{j,k+1}(n) + (n + j + 1) \, e_{j,k}(n)$ for all $j, k \in \mathbb{N}$;
$e_{j,k}(n) = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell} [j, j-k+\ell] \, (n + 1)^\ell$ for all
$k \le j$; and for all $j$, $\sum_{k=0}^{j} e_{j,k}(n) = (n + 2)^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k e_{j,k}(n) = (-1)^j n^{\overline{j}}$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Proposition 1.
