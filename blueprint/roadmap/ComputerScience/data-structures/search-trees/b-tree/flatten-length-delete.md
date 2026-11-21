# Deletion shortens the flattening by one exactly when the key is present

Let $t \ge 2$,
let $T$ be a B-tree of minimum degree $t$ over a linearly ordered key type, and let $x$ be a key.
If $x$ occurs in the inorder flattening of $T$, the flattening of the tree obtained from $T$ by
deleting $x$ (with minimum degree $t$) has length one less than the flattening of $T$; otherwise
the two flattenings have the same length.
