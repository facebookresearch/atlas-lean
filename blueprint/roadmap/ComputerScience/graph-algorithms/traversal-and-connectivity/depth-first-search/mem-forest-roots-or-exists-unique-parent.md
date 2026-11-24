# Every discovered vertex is a forest root or has a unique parent

Let $G$ be a finite
directed graph given by ordered adjacency lists, let $r$ be a list of root vertices, and let $v$
be a vertex in the preorder of the left-first depth-first search of $G$ from $r$. Then $v$ is a
forest root of that search, or there is exactly one vertex $p$ such that $(v, p)$ is among the
(child, parent) pairs recorded by the search.
