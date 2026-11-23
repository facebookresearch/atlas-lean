# The augmenting-path algorithm returns a matching

For every bipartite graph with left
vertices $0, \dots, a-1$, right vertices $0, \dots, b-1$ and an adjacency list for each left
vertex, the pairs $(i, j)$ such that the augmenting-path maximum matching algorithm (from the
empty matching, repeatedly flip an augmenting path found by the layered search) makes $i$ the
partner of $j$ form a matching of the graph: each pair is an edge, and no two distinct pairs
share a left or a right vertex.
