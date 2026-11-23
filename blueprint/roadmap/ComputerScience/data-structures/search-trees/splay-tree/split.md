# Search-path split at a key

Let $\alpha$ be a linearly ordered type, let $x \in \alpha$, and
write $(k; L, R)$ for the binary tree with root key $k$, left subtree $L$ and right subtree $R$.
The split of a binary tree with keys in $\alpha$ at $x$ is the pair of trees defined by
recursion: the empty tree splits into two empty trees; if $x < k$ and $L$ splits into
$(L_1, L_2)$, then $(k; L, R)$ splits into $(L_1, (k; L_2, R))$; if $k < x$ and $R$ splits into
$(R_1, R_2)$, then $(k; L, R)$ splits into $((k; L, R_1), R_2)$; and if $x = k$, then
$(k; L, R)$ splits into $(L, R)$.

When the tree is a binary search tree (at every node, the keys of the left subtree are strictly
smaller and those of the right subtree strictly larger than the node's key), the first part
holds the keys below $x$ and the second part the keys above $x$; the key $x$, if present, is
dropped.
