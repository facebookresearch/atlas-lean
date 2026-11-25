# Shortest path weight with at most $r$ edges

Let $w$ be an $n \times n$ matrix of
weights in $\mathbb{Z} \cup \{\infty\}$ on the vertices $\{0, \dots, n-1\}$, let $r$ be a natural
number, let $i$ and $j$ be vertices, and let $d \in \mathbb{Z} \cup \{\infty\}$. A weighted path
from $i$ to $j$ is a nonempty list $p$ of vertices that starts at $i$, ends at $j$ and has finite
weight on each pair of consecutive vertices; its number of edges is its length minus one, and its
weight $w(p)$ is the sum of the weights of its edges. Then $d$ is the shortest weight of a path
from $i$ to $j$ with at most $r$ edges when $d \le w(p)$ for every weighted path $p$ from $i$ to
$j$ with at most $r$ edges, and either $d = \infty$ or $d = w(p)$ for some weighted path $p$ from
$i$ to $j$ with at most $r$ edges.

Paths may repeat vertices; no absence-of-negative-cycles hypothesis is needed.
