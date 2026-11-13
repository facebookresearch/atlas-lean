# Recurrence for permutations counted by cycles and fixed points

Write $a(n, k, j)$ for the
number of permutations of an $n$-element set with exactly $k$ cycles (fixed points counted as
cycles of length one) and exactly $j$ fixed points. For all natural numbers $n$, $k$ and $j$
with $1 \le j \le k$, $j \, a(n, k, j) = n \, a(n - 1, k - 1, j - 1)$, where $n - 1$ is read as
$0$ when $n = 0$.

The paper assumes $n \ge k \ge 1$; the identity holds for all $n$.

## Sources

- Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*, INTEGERS 24 (2024), Article A54, Proposition 3 (iii).
