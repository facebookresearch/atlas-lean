# The characteristic property of suffix sums

Let $n$ nodes be linked into lists by a
partial successor function such that, starting from any node, $n$ steps run off the end of its
list, and let each node $v$ carry a value $x_v$ in an additive monoid $M$. Then for every node
$v$, the suffix sum of $v$ is $x_v$ plus the suffix sum of the successor of $v$, or just $x_v$
if $v$ has no successor.
