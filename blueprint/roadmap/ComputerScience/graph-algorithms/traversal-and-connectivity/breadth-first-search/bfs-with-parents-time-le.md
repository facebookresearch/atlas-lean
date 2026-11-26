# Linear bound on the cost of BFS with parents

Let $G$ be a finite directed graph with
vertex list $V$ and adjacency lists $\mathrm{adj}(u)$, and let $s$ be a vertex. The cost of
breadth-first search with parents from $s$, counting dequeue attempts, adjacency checks, enqueues
and parent writes, is at most $3|V| + \sum_{u \in V} |\mathrm{adj}(u)|$, where adjacency lists
are counted with repetitions.
