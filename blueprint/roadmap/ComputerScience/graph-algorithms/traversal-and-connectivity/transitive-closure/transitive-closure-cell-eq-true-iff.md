# Correctness of the transitive-closure algorithm

Let $A$ be a Boolean adjacency matrix
of a directed graph on the vertices $0, \dots, n-1$. For all vertices $i$ and $j$, the entry
$(i, j)$ of the matrix returned by the transitive-closure algorithm on $A$ is true if and only if
$j$ is reachable from $i$ by a sequence of zero or more edges of the graph.
