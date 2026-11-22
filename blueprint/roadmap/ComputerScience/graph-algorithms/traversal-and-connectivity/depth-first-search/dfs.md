# Left-first depth-first search

Given a directed graph $G$ with ordered adjacency lists
and an ordered list of roots, depth-first search processes the roots from left to right,
skipping roots already visited. Visiting an unvisited vertex $v$ marks it visited and records its
discovery, then processes the out-neighbours of $v$ in adjacency-list order, visiting each one
not yet visited at that moment and recording $v$ as its parent, and finally records that $v$ has
finished. The result is the traversal consisting of the vertices in discovery order (preorder),
the vertices in finish order (postorder), and the (child, parent) pairs in the order the children
were discovered.
