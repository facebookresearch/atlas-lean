# Kruskal's output is a sorted spanning forest

For every graph $G$, the edge list returned
by Kruskal's algorithm on $G$ is a spanning forest of $G$ (its edges are valid edges of $G$, it
is acyclic, and it connects the endpoints of every valid edge of $G$), and whenever an edge $e$
comes before an edge $f$ in it, the key (weight, input ordinal) of $e$ is lexicographically at
most that of $f$.
