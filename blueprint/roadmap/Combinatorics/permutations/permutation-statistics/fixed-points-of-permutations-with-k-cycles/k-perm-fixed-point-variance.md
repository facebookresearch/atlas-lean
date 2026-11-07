# Variance of the number of fixed points of a permutation with a given number of cycles

Write $a(n, k, j)$ for the number of permutations of an $n$-element set with exactly $k$ cycles
(fixed points counted as cycles of length one) and exactly $j$ fixed points, $c(n, k)$ for the
unsigned Stirling number of the first kind (the number of permutations of an $n$-element set
with $k$ cycles), and $\mu_{n,k} = n \, c(n - 1, k - 1) / c(n, k)$. If $2 \le k \le n$, then
$\frac{1}{c(n, k)} \sum_{j=0}^{k} j^2 \, a(n, k, j) - \mu_{n,k}^2 =
\mu_{n,k} (1 + \mu_{n-1,k-1} - \mu_{n,k})$.

Here $\mu_{n,k}$ is the mean number of fixed points of a uniformly random permutation of an
$n$-element set with $k$ cycles, so the left side is the variance of that number.

## Sources

- Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*, INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`).
