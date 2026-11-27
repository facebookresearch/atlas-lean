# Membership search in an AVL tree

For a linearly ordered type $\alpha$ and a key $x$,
the search for $x$ returns false on the empty tree; at a node with key $k$ it searches the left
subtree if $x < k$, searches the right subtree if $k < x$, and returns true otherwise. The cached
heights are ignored.
