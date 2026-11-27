# Ordered-and-valid check for interval trees

Keys of entries are pairs (low endpoint,
identifier), ordered lexicographically. Given optional lower and upper key bounds $\ell$ and $u$,
the check accepts the empty tree, and accepts a node with left subtree $L$, entry $e$ and right
subtree $R$ exactly when the key $k$ of $e$ is strictly greater than $\ell$ if $\ell$ is present
and strictly less than $u$ if $u$ is present, the interval of $e$ has low endpoint at most its
high endpoint, $L$ is accepted with bounds $\ell$ and $k$, and $R$ is accepted with bounds $k$
and $u$.
