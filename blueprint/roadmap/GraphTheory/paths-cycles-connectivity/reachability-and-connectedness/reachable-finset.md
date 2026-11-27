# Vertices reachable from a vertex

For a simple graph $G$ on a finite vertex set $V$ and
a vertex $u$, this is the set obtained from $\{u\}$ by breadth-first search with at most $|V|$
rounds, stopping early as soon as a round adds no new vertex.

It consists exactly of the vertices reachable from $u$ in $G$.
