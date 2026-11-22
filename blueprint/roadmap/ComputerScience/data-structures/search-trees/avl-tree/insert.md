# Insertion into an AVL tree

Let the keys be linearly ordered, and write
$\mathrm{balance}(L, k, R)$ for the AVL rebalancing of the node with left subtree $L$, key $k$ and
right subtree $R$. Inserting $x$ into the empty tree gives the node with key $x$, two empty
children and cached height $1$. Inserting $x$ into a node with left subtree $L$, key $k$ and right
subtree $R$ gives $\mathrm{balance}(L', k, R)$, where $L'$ is the result of inserting $x$ into $L$,
when $x < k$; it gives $\mathrm{balance}(L, k, R')$, where $R'$ is the result of inserting $x$
into $R$, when $k < x$; and otherwise it returns the node unchanged.
