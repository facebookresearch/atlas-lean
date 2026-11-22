# Insertion into a binary search tree

For a linearly ordered type $\alpha$, a key
$x \in \alpha$ and a binary tree $t$ with keys in $\alpha$, inserting $x$ into the empty tree gives
the single node with key $x$ and empty subtrees; inserting $x$ into a node with key $k$, left
subtree $L$ and right subtree $R$ inserts $x$ into $L$ when $x < k$, inserts $x$ into $R$ when
$k < x$, and returns the node unchanged when $x = k$.
