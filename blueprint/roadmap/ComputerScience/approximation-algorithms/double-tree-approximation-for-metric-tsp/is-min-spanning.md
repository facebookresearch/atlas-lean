# Minimum spanning tree of a vertex list

Let $d$ be a cost function on the vertices with
values in a linearly ordered additive commutative monoid. The tree with root $r$ and subtree
forest $F$ is a minimum spanning tree of a list $V$ of vertices for $d$ when it is a spanning tree
of $V$ (the vertices of $V$ are distinct and the list of $r$ followed by the vertices of $F$ in
preorder is a permutation of $V$) and, for every vertex $r'$ and forest $F'$ such that the tree
with root $r'$ and subtree forest $F'$ is a spanning tree of $V$, the weight of $F$ below $r$ is
at most the weight of $F'$ below $r'$.
