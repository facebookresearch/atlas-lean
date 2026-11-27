# The deleted key is absent after rebuild deletion

Let $t \ge 2$ and let $T$ be a B-tree of
minimum degree $t$ with keys in a linearly ordered type. For every key $x$, the tree obtained
from $T$ by rebuild deletion of $x$ (erasing $x$ from the inorder flattening of $T$ and
rebuilding a B-tree of minimum degree $t$ from the remaining keys) does not contain $x$.
