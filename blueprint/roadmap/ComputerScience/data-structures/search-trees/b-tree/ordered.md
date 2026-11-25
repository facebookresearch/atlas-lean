# Ordered B-tree

A B-tree over a type with a relation $<$ is ordered when its inorder
flattening is strictly increasing, that is, each key of the flattening is less than every
key that comes after it. This single condition packages sortedness of the keys at each node
and the separator bounds between a node's keys and the keys stored in its subtrees.
