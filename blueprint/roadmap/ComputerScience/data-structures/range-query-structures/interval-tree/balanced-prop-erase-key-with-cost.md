# Keyed deletion preserves AVL balance in an interval tree

Let $T$ be an interval tree that
is AVL balanced with exact stored heights, and let $k$ be a key (a pair of an integer low endpoint
and a natural-number identifier). The tree $T'$ returned by keyed deletion of $k$ from $T$ (the
tree component of the result; the cost is ignored) is again AVL balanced with exact stored
heights, and the height of $T'$ is either the height of $T$ or one less.
