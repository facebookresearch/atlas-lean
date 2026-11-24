# Balance theorem for splay trees

Let $t$ be a binary tree with $n$ nodes and keys in a linear order, and let $x_0, x_1, \dots$ be
keys (here $\log_2 0$ is taken to be $0$). Splay successively at
$x_0, \dots, x_{m-1}$, starting from $t$, and let $t_i$ be the tree before the $i$-th splay.
Then

$$\sum_{i<m} \mathrm{cost}(x_i, t_i) \le m\,(3 \log_2 n + 1) + n \log_2 n,$$

where the [cost](cost.md) of a splay is its number of rotations, or one if it performs none.
This is the explicit form of Sleator and Tarjan's Theorem 1: the total access time of $m$
accesses on an $n$-node splay tree is $O((m + n) \log n + m)$. Since the time of a search is
proportional to one plus the depth of the node reached, that depth is the number of rotations
of the splay that follows, and the cost of each splay is at least one, the bound covers the
searches as well, up to a constant factor.

## Informally uses

- [Amortized cost of a splay is at most $3 \log_2 n + 1$](amortized-cost-le.md): the
  per-operation bound.
- [Potential method with per-operation amortized bounds](../../amortized-analysis/sum-cost-le-of-amortized-cost-le.md):
  turns the per-operation bound into a bound on the sequence.
- [Upper bound on the splay-tree potential](potential-le.md) and [nonnegativity of the
  potential](potential-nonneg.md): bound the net potential drop by $n \log_2 n$.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, Theorem 1 (Balance Theorem).
