# Search in a red-black tree

Searching a red-black tree over a linearly ordered type for a
key $x$ returns a Boolean, ignoring colors: the empty tree gives false, and at a node with key $k$
the search continues in the left subtree if $x < k$, continues in the right subtree if $k < x$,
and returns true otherwise.
