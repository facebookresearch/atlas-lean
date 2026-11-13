# Size of a segment tree

The size of a segment tree is $0$ for the empty tree, $1$ for a
leaf, and, for an internal node, the segment length cached at that node.

When every cached length is the sum of the sizes of the node's children, this is the number of
leaves, and internal nodes answer in constant time.
