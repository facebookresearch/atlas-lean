# Pruning keeps the vertices outside the detached subtree

Let $t$ be a rooted tree
whose preorder vertex list has no repeated vertex, and let $x$ be a vertex. Suppose the
subtree search finds the subtree $s$ of $t$ rooted at $x$, and pruning $t$ at $x$ leaves
the tree $t'$. Then every vertex of $t$ that is not a vertex of $s$ is a vertex of $t'$.
