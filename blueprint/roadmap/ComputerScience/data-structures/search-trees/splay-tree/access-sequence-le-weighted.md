# Splay-tree access bound for arbitrary weights

Let $w$ be positive item weights, $t$ a binary search tree of total weight $W$ and
$x_0, \dots, x_{m-1}$ keys of $t$. Splaying successively at $x_0, \dots, x_{m-1}$, starting
from $t$, costs in total at most

$$\sum_{j<m} \Bigl(3 \log_2 \frac{W}{w(x_j)} + 1\Bigr) + \sum_{i \in t} \log_2 \frac{W}{w(i)}.$$

Each access has amortized cost at most $3 \log_2 (W / w(x_j)) + 1$, and over the sequence the
potential drops by at most $\sum_i \log_2 (W / w(i))$, because the subtree at the node holding
$i$ always has weight between $w(i)$ and $W$. Sleator and Tarjan obtain their balance,
static-optimality and static-finger theorems from this bound by choosing the weights.

## Informally uses

- [Amortized cost of accessing a present key](amortized-cost-le-weighted.md): the per-access
  bound.
- [Potential method with per-operation amortized bounds](../../amortized-analysis/sum-cost-le-of-amortized-cost-le.md)

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, the remark before Theorem 1 (net decrease in potential at most
  $\sum_i \log(W/w(i))$).
