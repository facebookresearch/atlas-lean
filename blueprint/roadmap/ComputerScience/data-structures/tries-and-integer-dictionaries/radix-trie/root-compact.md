# Path-compressed root

A radix trie is path-compressed at its root when its root node stores
a value or has at least two child edges.

A value-free node with at most one child could be merged into the edge above it, which a radix
trie rules out for every node reached by an edge; the root of the whole trie has no incoming edge
and is exempt.
