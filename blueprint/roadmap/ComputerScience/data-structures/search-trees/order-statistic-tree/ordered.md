# Ordered order-statistic tree

An order-statistic tree over a type equipped with a
relation $<$ is ordered when the binary tree obtained by erasing its cached sizes is an ordered
binary search tree: at every node, each key of the left subtree is $<$ the node's key, the
node's key is $<$ each key of the right subtree, and both subtrees are ordered.
