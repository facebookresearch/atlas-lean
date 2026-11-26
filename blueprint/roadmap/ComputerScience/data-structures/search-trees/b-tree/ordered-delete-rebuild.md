# Rebuild deletion yields an ordered tree

Let $t \ge 2$ and let keys come from a linearly
ordered type. For every key $x$ and every tree $T$, not necessarily ordered, the tree obtained
from $T$ by rebuild deletion of $x$ (removing the first occurrence of $x$, if any, from the
inorder flattening of $T$ and rebuilding a B-tree of minimum degree $t$ from the remaining keys)
is ordered: its inorder flattening is strictly increasing.
