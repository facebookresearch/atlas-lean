# Deletion from a binary search tree

Let $x$ be a key of a linearly ordered type. Deleting $x$
from the empty tree gives the empty tree. Deleting $x$ from a tree with root key $k$, left subtree
$L$ and right subtree $R$ gives the tree with root key $k$, left subtree $L$ with $x$ deleted and
right subtree $R$ if $x < k$; the tree with root key $k$, left subtree $L$ and right subtree $R$
with $x$ deleted if $k < x$; and the join of $L$ and $R$ otherwise, that is, if $x = k$.
