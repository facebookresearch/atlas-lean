# Treap lookup finds exactly the stored entries

Let $t$ be a tree with keys in a linearly
ordered type that is ordered as a binary search tree (every key in a left subtree is smaller and
every key in a right subtree is larger than the node's key). For every key $k$ and value $v$,
looking up $k$ in $t$ returns $v$ if and only if $t$ has a node with key $k$ and value $v$, for
some priority.
