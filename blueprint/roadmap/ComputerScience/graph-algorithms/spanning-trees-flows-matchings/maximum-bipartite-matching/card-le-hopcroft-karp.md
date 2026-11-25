# Correctness of Hopcroft–Karp

Let a bipartite graph have left vertices $\{0, \dots, a - 1\}$, right vertices
$\{0, \dots, b - 1\}$ and, for each left vertex, a list of its right neighbours. Every matching of
the graph (a set of edges in which no vertex occurs twice) has at most as many edges as the
matching returned by the Hopcroft–Karp algorithm started from the empty matching.
