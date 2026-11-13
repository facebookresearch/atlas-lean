# Johnson's algorithm

Let $E$ be a list of directed edges on the vertices
$\{0, \dots, n-1\}$ with integer weights. Johnson's algorithm adds a new vertex $s$ with an
edge of weight $0$ to every original vertex and runs Bellman–Ford from $s$. If Bellman–Ford
reports a negative cycle, the algorithm returns no table. Otherwise let $h(v)$ be the
Bellman–Ford distance of $v$ (taken to be $0$ if $v$ is unreached). Each edge from $u$ to $v$ of
weight $w$ gets the new weight $\max(0, w + h(u) - h(v))$.
For each original vertex $u$ the algorithm runs Dijkstra from $u$ on the original vertices,
where the weight from $x$ to $y$ is the least new weight of an edge from $x$ to $y$. It
returns the table whose entry at $(u, v)$ is $\infty$ if Dijkstra does not reach $v$, and
$d'(u, v) + h(v) - h(u)$ otherwise, where $d'(u, v)$ is the Dijkstra distance.

The cost counts the selected construction, scan, relaxation and decoding actions, not full RAM
or bit complexity.
