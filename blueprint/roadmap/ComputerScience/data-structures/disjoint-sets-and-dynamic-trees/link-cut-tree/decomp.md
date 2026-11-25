# Preferred-path decomposition of a tree

Given a list $E$ of preferred edges, each a pair
(parent, preferred child), the decomposition of a tree $T$ is a pair (down, rest): down is the
preferred path that starts at the root of $T$ and follows edges of $E$ downward, and rest is the
list of all other preferred paths of $T$. When a node has several children joined to it by edges
of $E$ (excluded in valid states, where each vertex has at most one preferred child), the first
one in child order continues the path through that node and each of the others starts its own
path in rest.
