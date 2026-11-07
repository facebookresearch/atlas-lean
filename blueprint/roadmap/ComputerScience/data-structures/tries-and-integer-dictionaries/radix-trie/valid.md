# Valid radix trie

Validity of radix tries is defined inductively: a node is valid when every
label of its child edges is nonempty, the first symbols of the labels of its child edges are
pairwise distinct, and for each child edge the subtree at its end is valid and path-compressed at
its root (its root stores a value or has at least two child edges).

Thus every value-free node other than the root has at least two children, so no unary value-free
node remains to be merged into its parent edge.
