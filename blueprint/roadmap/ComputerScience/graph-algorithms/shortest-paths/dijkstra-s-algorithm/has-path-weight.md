# Walks of a given weight

Let $G$ be a directed graph given by adjacency lists, let
$w(u, v) \in \mathbb{N}$ be a weight for each ordered pair of vertices, let $s$ and $t$ be
vertices and let $d$ be a natural number. Then $s$ reaches $t$ with weight $d$ when there is a
nonempty list of vertices $v_0, v_1, \dots, v_k$ with $v_0 = s$, $v_k = t$ and each $v_{i+1}$ in
the adjacency list of $v_i$, such that $w(v_0, v_1) + \dots + w(v_{k-1}, v_k) = d$.
