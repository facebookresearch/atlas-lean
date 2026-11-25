# Total number of fixed points of permutations with a given number of cycles

For natural
numbers $n$, $k$ and $j$, let $a(n, k, j)$ be the number of permutations of an $n$-element set
with exactly $k$ cycles (fixed points counted as cycles of length one) and exactly $j$ fixed
points, and let $c(n, k)$ be the unsigned Stirling number of the first kind. Then for every
natural number $n$ and every $k \ge 1$,

$$\sum_{j=0}^{k} j \, a(n, k, j) = n \, c(n - 1, k - 1),$$

where the right-hand side is read as $0$ when $n = 0$.

Dividing by $c(n, k)$, the number of permutations of an $n$-element set with $k$ cycles, gives the
mean $\mu_{n,k} = n \, c(n - 1, k - 1) / c(n, k)$ of the number of fixed points of a uniformly
random such permutation when $n \ge k$.

## Sources

- Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*, INTEGERS 24 (2024), Article A54, Proposition 4.
