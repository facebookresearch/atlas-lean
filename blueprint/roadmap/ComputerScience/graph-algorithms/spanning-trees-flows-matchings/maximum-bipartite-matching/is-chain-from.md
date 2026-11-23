# Alternating chain to an unmatched left vertex

In a bipartite graph, let each right vertex
have at most one partner, a left vertex (the partners need not form a matching), and let $z$ be a
right vertex. A list $Q$ of pairs (left vertex, right vertex) is an alternating chain from $z$
when its first pair has right vertex $z$, each of its pairs $(i, j)$ is an edge with $i$ not the
partner of $j$, each right vertex after the first is the partner of the preceding left vertex,
and its last left vertex is the partner of no right vertex.

Unlike an augmenting path, $z$ may be matched, the vertices need not lie in the layers of the
search, and a vertex may occur more than once.
