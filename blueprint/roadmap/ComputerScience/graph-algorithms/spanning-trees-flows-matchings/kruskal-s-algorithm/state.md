# Kruskal scan state

A state of the Kruskal scan on the vertices $\{0, \dots, n-1\}$
consists of a union-find parent forest on these vertices, which records the current partition,
and the list of edges accepted so far, newest first.
