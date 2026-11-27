# Segment sums add up

Let $\mathrm{succ}$ be a partial successor function on nodes
$0, \dots, n-1$ and $x_v$ values in an additive monoid $M$. For $k \in \mathbb{N}$ write
$S_k(v)$ for the sum, in list order, of the values of the nodes reached from $v$ in
$0, 1, \dots, k - 1$ steps along $\mathrm{succ}$ (a missing node contributes $0$). Then for all
$a, b \in \mathbb{N}$ and every node $v$, $S_{a+b}(v) = S_a(v) + S_b(u)$ if the node $u$ reached
from $v$ in $a$ steps exists, and $S_{a+b}(v) = S_a(v)$ otherwise.
