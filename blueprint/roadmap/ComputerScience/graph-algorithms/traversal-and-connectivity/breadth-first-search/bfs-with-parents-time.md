# Exact cost of BFS with parents

Let $G$ be a finite directed graph with vertex list $V$
and adjacency lists $\mathrm{adj}(u)$, let $s$ be a vertex, and let $L$ be the list of vertices in
the order in which breadth-first search from $s$ discovers them. The cost of breadth-first search
with parents from $s$, counting dequeue attempts, adjacency checks, enqueues and parent writes,
equals $|V| + \sum_{u \in L} |\mathrm{adj}(u)| + |L| + (|L| - 1)$, where adjacency lists are
counted with repetitions and $|L| - 1$ is truncated at $0$.
