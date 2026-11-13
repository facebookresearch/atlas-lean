# The invariant of pointer jumping for list ranking

Let $\mathrm{succ}$ map each of the
nodes $0, \dots, n - 1$ to its successor or to nothing, and suppose the lists terminate: from
every node, $n$ steps run off the end. Write $\mathrm{rank}(v)$ for the number of nodes after
$v$. Then for every $t \ge 0$ and every node $v$, after $t$ rounds of pointer jumping, the
pointer of $v$ is the node $2^t$ steps down the list from $v$ (no node if the list ends before
that), and the distance of $v$ is $\min(2^t, \mathrm{rank}(v))$.
