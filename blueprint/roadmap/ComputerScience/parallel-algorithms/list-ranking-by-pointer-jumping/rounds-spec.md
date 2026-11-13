# The invariant of pointer jumping for suffix sums

Let $\mathrm{succ}$ be a partial
successor function on nodes $0, \dots, n-1$ and $x_v$ values in an additive monoid $M$. For
every $t \in \mathbb{N}$ and every node $v$, after $t$ rounds of pointer jumping the pointer of
$v$ is the node reached from $v$ in $2^t$ steps along $\mathrm{succ}$ (undefined if the list
ends sooner), and the sum of $v$ is the sum, in list order, of the values of the nodes reached
from $v$ in $0, 1, \dots, 2^t - 1$ steps (a missing node contributes $0$).
