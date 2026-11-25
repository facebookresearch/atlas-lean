# Keyed insertion preserves AVL balance in an interval tree

Let $T$ be an interval tree that
is AVL balanced with exact stored heights, and let $e$ be an entry. The tree $T'$ returned by keyed
insertion of $e$ into $T$ (which replaces an entry with the same key, if there is one; we take the
tree component of the result and ignore the cost) is again AVL balanced with exact stored heights,
and the height of $T'$ is either the height of $T$ or one more.
