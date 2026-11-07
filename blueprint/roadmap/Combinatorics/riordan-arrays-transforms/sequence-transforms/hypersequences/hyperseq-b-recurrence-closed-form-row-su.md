# Recurrence, closed form and row sums of Parisse's $b_{j,k}(n)$

Let $n \in \mathbb{N}$ and
let $b_{j,k}(n)$ be the entries of Parisse's matrix $B(n)$. Write $[j, \ell]$ for the unsigned
Stirling numbers of the first kind and $x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the
rising factorial. Then $b_{0,k}(n) = \delta_{0,k}$ for all $k$; for all $j, k \in \mathbb{N}$,
$b_{j+1,0}(n) = (n + j + 1) \, b_{j,0}(n)$ and
$b_{j+1,k+1}(n) = (n + j + 1) \, b_{j,k+1}(n) - b_{j,k}(n)$;
$b_{j,k}(n) = (-1)^k \sum_{\ell=k}^{j} \binom{\ell}{k} [j, \ell] \, (n + 1)^{\ell-k}$ for all
$j, k$ (an empty sum for $k > j$); and for all $j$,
$\sum_{k=0}^{j} b_{j,k}(n) = n^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k b_{j,k}(n) = (n + 2)^{\overline{j}}$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Proposition 2 (`integers-2026-A36-prop-2`).
