# Consistent heuristic

Let $G$ be a directed graph on the vertices $\{0, \dots, n-1\}$ and
let $w$ assign a natural number $w(u, v)$ to each pair of vertices. A heuristic $h$ assigning a
natural number to each vertex is consistent (monotone) if $h(u) \le w(u, v) + h(v)$ for every
edge $u \to v$ of $G$.
