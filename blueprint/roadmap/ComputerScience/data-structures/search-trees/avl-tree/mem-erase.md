# Keys of an ordered AVL tree after deletion

Let $T$ be a binary tree with cached heights
over a linearly ordered type, ordered as a search tree (every key in a left subtree is smaller,
and every key in a right subtree is larger, than the key at the node). Then for all keys $x$
and $y$, $y$ occurs in the tree obtained by deleting $x$ from $T$ if and only if $y$ occurs in
$T$ and $y \ne x$.
