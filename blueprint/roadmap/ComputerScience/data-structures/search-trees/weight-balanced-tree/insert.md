# Weight-balanced insertion

For a key $x$ of a linearly ordered type, the insertion
$\mathrm{insert}(x, t)$ of $x$ into a binary tree $t$ is defined by recursion on $t$. Into the
empty tree it gives the single node with key $x$. Into the node $N$ with key $k$, left subtree
$L$ and right subtree $R$ it gives $\mathrm{balance}(\mathrm{insert}(x, L), k, R)$ if $x < k$,
$\mathrm{balance}(L, k, \mathrm{insert}(x, R))$ if $k < x$, and $N$ itself if $x = k$, where
$\mathrm{balance}$ is weight-balanced rebalancing.
