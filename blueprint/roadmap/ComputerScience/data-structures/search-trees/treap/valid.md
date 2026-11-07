# Valid treap

A binary tree whose nodes each carry a key, a value and a natural-number
priority, with keys compared by a relation $<$ (any `LT` instance; no order axioms are
assumed), is a valid treap when it satisfies both of the following at every node: every key in
the left subtree is less than the node's key and the node's key is less than every key in the
right subtree (search-tree order with respect to $<$), and the node's priority is at most the
priority of every node in its left and right subtrees (min-heap order on priorities).
