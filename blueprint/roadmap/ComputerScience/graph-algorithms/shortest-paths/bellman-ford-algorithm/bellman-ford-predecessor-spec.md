# Bellman-Ford predecessor edges are tight

Let $E$ be a list of integer-weighted directed
edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. Suppose Bellman-Ford run on
$E$ from $s$ returns distances $d$ together with predecessor edges, and the predecessor edge of a
vertex $t$ is an edge $e$ from $u$ to $v$ of weight $w$. Then $e$ belongs to $E$, $v = t$, and
$d(u)$ and $d(t)$ are both finite with $d(t) = d(u) + w$.
