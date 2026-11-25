# Distance-guided path reconstruction

Let $G$ be a directed graph with ordered adjacency
lists, $d$ a partial labelling of its vertices by natural numbers, $t$ a vertex, and $\equiv$ a
given Boolean test on pairs of vertices (not required to be equality). The reconstruction from
a vertex $u$ with $k$ steps left returns the one-element list $[u]$ when $k = 0$ and $u \equiv t$
holds, and fails when $k = 0$ and $u \equiv t$ fails. When $k \ge 1$, it takes the first
out-neighbour $w$ of $u$ in adjacency order with $d(w) = k - 1$; it fails if there is none, and
otherwise returns $u$ followed by the reconstruction from $w$ with $k - 1$ steps left, failing
if that fails.
