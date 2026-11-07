# Root invariant of a B-tree

For a minimum degree $t$ and a height $h$, a tree
satisfies the root invariant when either $h = 0$ and the tree is a leaf with at most
$2t - 1$ keys (possibly none, for the empty tree), or $h = h' + 1$ and the tree is an
internal node with between $1$ and $2t - 1$ keys and exactly one more child than keys,
every child satisfying the structural invariant for minimum degree $t$, minimum top-node
key count $t - 1$ and height $h'$. Here $2t - 1$ and $t - 1$ are truncated at $0$.
