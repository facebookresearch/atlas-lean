# Greedy run on an array

In a bipartite graph with left vertices $0, \dots, a - 1$ and right
vertices $0, \dots, b - 1$, start from an array whose entry $k$ holds the partner of the right
vertex $k$, a missing entry meaning no partner, and let the right vertices of a list $L$ arrive one
after another in the order of $L$. Each arrival performs the greedy step on the array: the entry of
the arriving vertex $j$ is set to the first left neighbour of $j$, in the order $0, \dots, a - 1$,
that is free, that is, the partner of none of the right vertices $0, \dots, b - 1$ in the current
array, or to none if no neighbour of $j$ is free; if the array has no entry $j$, it is unchanged.
