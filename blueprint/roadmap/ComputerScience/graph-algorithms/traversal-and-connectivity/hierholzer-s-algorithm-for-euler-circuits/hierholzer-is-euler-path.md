# Hierholzer's algorithm finds Euler paths in directed multigraphs

Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be
vertices such that $G$ is semi-balanced for $s$ and $t$ (at $s$ one more edge occurrence leaves
than enters, at $t$ one more enters than leaves, and at every other vertex as many leave as enter;
at every vertex when $s = t$) and the source of every edge of $G$ is reachable from $s$. Then the
vertex sequence returned by Hierholzer's algorithm on $G$ from $s$ is an Euler path of $G$ from $s$
to $t$.
