# Cached maximum of an interval tree

The cached maximum of an interval tree is no value
when the tree is empty, and when the tree is a node it is the integer stored in the node's cached
maximum-high-endpoint field.

It is read in constant time. The tree type itself does not require this field to equal the
largest high endpoint of an interval in the subtree.
