# Treap inorder contents split at a pivot

Let the keys come from a linearly ordered type,
let $t$ be a tree and $k$ a pivot key, and let splitting $t$ at $k$ produce a lower tree $L$, an
optional value-priority pair found at $k$, and an upper tree $G$. Then the inorder list of
key-value pairs of $t$ is the inorder list of $L$, followed by $(k, v)$ if the split found a pair
with value $v$ (and by nothing if it found none), followed by the inorder list of $G$.
