# Breadth-first search with parents returns the ordinary BFS result

For every finite
directed graph $G$ with ordered adjacency lists and every source vertex $s$, the output of
breadth-first search with parents from $s$ in $G$, with its cost and its predecessor table
forgotten, equals the result of ordinary FIFO breadth-first search from $s$ in $G$: the same
distance table and the same first-discovery order.
