# Erasing the size caches of an order-statistic tree

The erasure of an order-statistic
tree is the binary tree of the same shape whose node keys are the keys of the original nodes:
the empty tree is sent to the empty tree, and a node is sent to the node with the same key
whose left and right subtrees are the erasures of the original left and right subtrees, so
every cached subtree size is dropped.
