# Membership after rebuild deletion from a B-tree

Let $t \ge 2$ and let $T$ be a B-tree of
minimum degree $t$ with keys in a linearly ordered type. For all keys $x$ and $y$, the key $y$
lies in the tree obtained from $T$ by rebuild deletion of $x$ (erasing $x$ from the inorder
flattening of $T$ and rebuilding a B-tree of minimum degree $t$ from the remaining keys) if and
only if $y \ne x$ and $y$ lies in $T$.
