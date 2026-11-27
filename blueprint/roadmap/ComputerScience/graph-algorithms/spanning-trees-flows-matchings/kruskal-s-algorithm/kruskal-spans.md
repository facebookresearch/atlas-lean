# Kruskal's selected edges span the graph

For every finite weighted multigraph $G$ on the
vertices $\{0, \dots, n-1\}$, given by its list of input edges, and every valid input edge of $G$
(one whose endpoints are both less than $n$), the two endpoints of that edge are connected by the
edges that Kruskal's algorithm selects on $G$.

The graph $G$ need not be connected.
