# Keyed insertion preserves the interval-tree cache invariant

Let $T$ be an interval tree
satisfying the cache invariant (every cached maximum high endpoint, height and size is exact), and
let $e$ be an entry. The tree returned by keyed insertion of $e$ into $T$ (the tree component of
the result; the cost is ignored) also satisfies the cache invariant. This includes the case where
an entry with the same key is replaced.
