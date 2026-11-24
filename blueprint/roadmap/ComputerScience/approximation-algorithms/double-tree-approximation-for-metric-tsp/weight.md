# Weight of a forest below a vertex

For a cost function $d$ and a vertex $p$, the weight
of a forest hanging below $p$ is the total cost of its tree edges: each top-level vertex $v$ is
joined to $p$ by an edge of cost $d(p, v)$, and each vertex $u$ is joined to each of its children
$c$ by an edge of cost $d(u, c)$. The empty forest has weight $0$.
