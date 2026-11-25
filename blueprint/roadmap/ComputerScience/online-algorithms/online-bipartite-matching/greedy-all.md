# The greedy online matching

In a bipartite graph with left vertices $0, \dots, a - 1$ and
right vertices $0, \dots, b - 1$, the greedy online matching is the partner array obtained by
starting from the empty matching and letting the right vertices arrive in the order
$0, 1, \dots, b - 1$, each arriving vertex being matched to its first free left neighbour in the
order $0, \dots, a - 1$, or left unmatched if no neighbour is free.

It is computed on arrays, with one array write per arrival.
