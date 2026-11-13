# Treap inorder contents after insertion

Let the keys come from a linearly ordered type,
let $t$ be a tree, $k$ a key, $v$ a value and $n$ a natural-number priority, and let $L$ and $G$
be the lower and upper trees produced by splitting $t$ at $k$. Then the inorder list of key-value
pairs of the tree obtained by inserting $k$ with value $v$ and priority $n$ into $t$ is the
inorder list of $L$, followed by $(k, v)$, followed by the inorder list of $G$.
