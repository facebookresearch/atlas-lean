# Height of a B-tree along first children

The height of a B-tree is computed by
following first children: a leaf has height $0$, an internal node with no children has height
$0$, and an internal node whose first child is $c$ has height one more than the height of $c$.

If a tree satisfies the B-tree structural invariant (or the root invariant) at height $h$,
then this height equals $h$.
