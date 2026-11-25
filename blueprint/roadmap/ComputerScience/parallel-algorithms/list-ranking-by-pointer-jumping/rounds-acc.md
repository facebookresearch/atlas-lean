# Pointer-jumping sums are the suffix sums once $n \le 2^t$

Let $\mathrm{succ}$ be a
partial successor function on nodes $0, \dots, n-1$ under which every list ends, that is, from
every node, the node reached in $n$ steps along $\mathrm{succ}$ is undefined, and let $x_v$ be
values in an additive monoid $M$. If $t \in \mathbb{N}$ satisfies $n \le 2^t$, then for every
node $v$ the sum of $v$ after $t$ rounds of pointer jumping is the suffix sum of $v$: the sum, in
list order, of the values from $v$ to the end of its list.
