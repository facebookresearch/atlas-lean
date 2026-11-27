# Cutting off the subtree at a vertex

Cutting at a vertex $x$ resets the preferred edges
of the state to the empty list and changes its forest as follows. If no tree of the forest
contains $x$, the forest is unchanged. Otherwise let $T$ be the first tree containing $x$ and
$S$ the first subtree of $T$ rooted at $x$ in preorder. Every tree containing $x$ is removed from
the forest, and two trees are appended at the end: first the remainder of $T$ with every subtree
rooted at $x$ pruned off, then $S$. When $x$ is the root of $T$ nothing remains, and only $S$ is
appended.
