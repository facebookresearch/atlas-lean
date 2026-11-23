# The pager misses every request

Let $k \in \mathbb{N}$ and let $A$ be a deterministic online pager with cache size $k$ on the
$k + 1$ pages $0, \dots, k$. For every $n \in \mathbb{N}$ and every state $q$ of $A$, the pager $A$
started in $q$ misses every request of the adversary's sequence of $n$ requests from $q$: its
number of misses on that sequence is exactly $n$.
