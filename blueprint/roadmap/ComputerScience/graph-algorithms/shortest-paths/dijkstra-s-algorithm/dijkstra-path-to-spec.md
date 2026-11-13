# Reconstructed Dijkstra paths are simple and have the output weight

Let $G$ be a directed
graph on the vertices $0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every
ordered pair of vertices, and let $s$ and $t$ be vertices. Suppose that following the
predecessor pointers output by Dijkstra's algorithm on $G$ with weights $w$ from source $s$
reconstructs a list of vertices $P$ for $t$. Then $P$ is nonempty, say $P = v_0, \dots, v_k$,
with $v_0 = s$ and $v_k = t$; there is an edge from each $v_{i-1}$ to $v_i$; the $v_i$ are
pairwise distinct; and the distance $d$ output for $t$ is finite with
$d = \sum_{i=1}^{k} w(v_{i-1}, v_i)$.
