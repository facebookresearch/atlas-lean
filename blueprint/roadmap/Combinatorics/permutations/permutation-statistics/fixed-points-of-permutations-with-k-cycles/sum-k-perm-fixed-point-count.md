# Stirling numbers from fixed-point counts

For natural numbers $n$, $k$ and $j$, let
$a(n, k, j)$ be the number of permutations of an $n$-element set with exactly $k$ cycles (fixed
points counted as cycles of length one) and exactly $j$ fixed points. Then for all natural
numbers $n$ and $k$,

$$\sum_{j=0}^{k} a(n, k, j) = c(n, k),$$

where $c(n, k)$ is the unsigned Stirling number of the first kind.

The paper assumes $n \ge k \ge 1$; the identity is stated for all $n$ and $k$.

## Sources

- Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*, INTEGERS 24 (2024), Article A54, Proposition 3 (iv) (`integers-2024-A54-prop-3`).
