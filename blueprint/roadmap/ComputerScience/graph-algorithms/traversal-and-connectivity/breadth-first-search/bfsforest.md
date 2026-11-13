# Breadth-first search forest

A breadth-first search forest on a vertex type $V$ consists
of a breadth-first search result, namely a partial distance function from $V$ to the natural
numbers and a list of vertices, together with a partial predecessor function from $V$ to $V$.
For a search from a source vertex $s$, these are meant to give the distance from $s$ of each
reachable vertex, the reachable vertices in first-discovery order, and the vertex from which
each reachable vertex other than $s$ was first discovered, with $s$ and the unreachable vertices
having no predecessor; the structure itself imposes none of these properties.
