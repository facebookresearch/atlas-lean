# Key tree of a treap

Let $\kappa$ be a type of keys and $\nu$ a type of values; a treap tree is empty or a node made of a left subtree, a key, a value, a natural-number priority and a right subtree. The key tree of a treap tree $t$ is the binary tree of the same shape that keeps only the keys: the empty treap tree goes to the empty binary tree, and a node with left subtree $L$, key $k$, any value and any priority, and right subtree $R$ goes to the binary-tree node with key $k$ whose left and right subtrees are the key trees of $L$ and $R$. Values and priorities are forgotten.
