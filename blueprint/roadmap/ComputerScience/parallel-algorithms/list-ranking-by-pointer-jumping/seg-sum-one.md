# Segment sums of unit values count nodes

Let $n$ nodes be linked into lists by a
partial successor function such that, starting from any node, $n$ steps run off the end of its
list, and give every node the value $1 \in \mathbb{N}$. Then for every $k \in \mathbb{N}$ and
every node $v$, the segment sum of length $k$ from $v$ (the sum of the values of the first $k$
nodes from $v$, fewer at the end of the list) is $\min(k, \operatorname{rank}(v) + 1)$, where
$\operatorname{rank}(v)$ is the number of nodes after $v$ in its list.
