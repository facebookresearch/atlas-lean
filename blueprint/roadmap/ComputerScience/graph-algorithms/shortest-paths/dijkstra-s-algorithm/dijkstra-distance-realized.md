# Dijkstra's finite distances are realized by walks

Let $G$ be a directed graph on the
vertices $0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every ordered pair of
vertices, and let $s$ and $t$ be vertices. If Dijkstra's algorithm on $G$ with weights $w$ from
source $s$ outputs a finite distance $d$ for $t$, then $G$ has a walk
$s = v_0, v_1, \dots, v_k = t$, with an edge from each $v_{i-1}$ to $v_i$, of weight
$\sum_{i=1}^{k} w(v_{i-1}, v_i) = d$.
