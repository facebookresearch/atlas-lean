# Search paths are alternating paths through unused vertices

Suppose the partner array
describes a matching, $k$ is a level and $j$ is a right vertex reached within $k + 1$ rounds of the
alternating breadth-first search. For every set of used left vertices and every set of dead right
vertices, if the search at level $k$ from $j$ finds a path $P$, then $P$ is an alternating path at
level $k$ from $j$, no left vertex of $P$ is used, and no right vertex of $P$ was dead before the
search.
