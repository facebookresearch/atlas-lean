# Greedy step on an array

In a bipartite graph with left vertices $0, \dots, a - 1$ and right
vertices $0, \dots, b - 1$, take an array whose entry $k$ holds the partner of the right vertex $k$,
a missing entry meaning no partner. On the arrival of a right vertex $j$, entry $j$ is set to the
first left neighbour of $j$, in the order $0, \dots, a - 1$, that is free, that is, the partner of
none of the right vertices $0, \dots, b - 1$ in the array, or to none if no neighbour of $j$ is
free; if the array has no entry $j$, it is unchanged.

Storing the partners in an array computes each choice once per arrival; evaluating the composed
function updates of the specification directly would recompute every earlier choice at each
lookup, a cost exponential in the number of right vertices.
