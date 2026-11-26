# Low-endpoint ordered interval tree

The empty tree is low-endpoint ordered, and a node is
low-endpoint ordered when both of its subtrees are low-endpoint ordered, every interval in the
left subtree has low endpoint at most the low endpoint of the node's interval, and the node's
low endpoint is at most the low endpoint of every interval in the right subtree.
