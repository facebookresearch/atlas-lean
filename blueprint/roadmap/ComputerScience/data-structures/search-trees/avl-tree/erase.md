# AVL tree deletion

Let $\alpha$ be a linearly ordered type and $x \in \alpha$. Deleting $x$
from a tree with cached heights is defined by recursion on the tree, where $\mathrm{balance}$
denotes the AVL rebalancing function. The empty tree stays empty. For a node with left subtree
$l$, key $k$ and right subtree $r$: if $x < k$, the result is $\mathrm{balance}(l', k, r)$, where
$l'$ is $l$ with $x$ deleted; if $k < x$, the result is $\mathrm{balance}(l, k, r')$, where $r'$
is $r$ with $x$ deleted; if $x = k$, the node is replaced by $r$ when $l$ is empty, by $l$ when
$r$ is empty, and otherwise by $\mathrm{balance}(l, m, r'')$, where $m$ is the leftmost key of
$r$ and $r''$ is $r$ with its leftmost key removed.
