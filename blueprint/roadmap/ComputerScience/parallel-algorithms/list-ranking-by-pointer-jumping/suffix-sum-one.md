# List ranking is the special case of unit values

Let $n$ nodes be linked into lists by
a partial successor function such that, starting from any node, $n$ steps run off the end of
its list. If every node has value $1 \in \mathbb{N}$, then the suffix sum of every node $v$ is
$\operatorname{rank}(v) + 1$, where $\operatorname{rank}(v)$ is the number of nodes after $v$ in
its list.
