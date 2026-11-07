# Stirling-type recursion for the mesh-pattern counting polynomial

Let $1 < k \le n$ and
$j > 0$. For a permutation $\sigma$ of $m$ elements, with positions numbered $1, \dots, m$, let
$p$ be the position of its largest value and let $N_r(\sigma)$ be the number of positions $i$
such that $\sigma(t) < \sigma(i)$ for all $t < i$ and at least $r - 1$ positions $t$ with
$i < t < p$ have $\sigma(t) > \sigma(i)$, plus $1$ if $p \ge r$. Let $P_{m,r}(X) \in \mathbb{N}[X]$
be the sum of $X^{N_r(\sigma)}$ over all permutations $\sigma$ of $m$ elements, and let
$c_{m,r}(s)$ be its coefficient of $X^s$. Then
$c_{n,k}(j) = (n-1)\,c_{n-1,k}(j) + c_{n-1,k}(j-1)$,
$P_{n,k}(X) = (X + n - 1)\,P_{n-1,k}(X)$, $c_{n,k}(0) = (n-1)\,c_{n-1,k}(0)$, and
$P_{k-1,k}(X) = (k-1)!$.

## Sources

- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1, Theorem (label `thm:main`), line 175, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
