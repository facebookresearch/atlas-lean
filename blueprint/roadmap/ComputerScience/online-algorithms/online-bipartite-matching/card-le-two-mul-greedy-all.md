# Greedy online matching is $1/2$-competitive

Consider a bipartite graph with left vertices $0, \dots, a - 1$ and right vertices
$0, \dots, b - 1$. Every matching $M$ of the graph has at most twice as many edges as the greedy
online matching, in which the right vertices arrive in the order $0, 1, \dots, b - 1$ and each is
matched to its first free left neighbour.

An edge of $M$ whose right vertex the greedy algorithm matched is charged to that right vertex,
any other edge to its left vertex, which the greedy algorithm matched by maximality; a matching
charges each greedy edge at most once on each side.
