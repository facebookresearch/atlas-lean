# Removing the minimum preserves AVL balance in an interval tree

Let $T$ be an interval tree
that is AVL balanced with exact stored heights. If removing the leftmost entry of $T$ succeeds and
returns an entry $m$, a remaining tree $R$ and a cost $c$, then $R$ is AVL balanced with exact
stored heights, and the height of $R$ is either the height of $T$ or one less.
