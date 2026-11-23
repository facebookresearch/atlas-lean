# Static optimality of splay trees

Let $t$ be a binary search tree and $x_0, \dots, x_{m-1}$ keys of $t$ in which every key
$i$ of $t$ occurs $q(i) \ge 1$ times. Splaying successively at $x_0, \dots, x_{m-1}$, starting
from $t$, costs in total at most

$$m + 3 \sum_{i \in t} q(i) \log_2 \frac{m}{q(i)} + \sum_{i \in t} \log_2 \frac{m}{q(i)},$$

which is $O\bigl(m + \sum_i q(i) \log (m / q(i))\bigr)$ (the last sum is at most the middle
one since $1 \le q(i) \le m$). In Sleator and Tarjan's words, for sufficiently long access
sequences splay trees are as efficient, to within a constant factor, as static optimum search
trees, without knowing the frequencies.

## Informally uses

- [Splay-tree access bound for arbitrary weights](access-sequence-le-weighted.md): with the
  weights $w(i) = q(i)$, whose total is $m$.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, Theorem 2 (Static Optimality Theorem).
