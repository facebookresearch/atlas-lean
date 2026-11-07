# Keyed deletion preserves the interval-tree cache invariant

Let $T$ be an interval tree
satisfying the cache invariant (every cached maximum high endpoint, height and size is exact), and
let $k$ be a key (a pair of an integer low endpoint and a natural-number identifier). The tree
returned by keyed deletion of $k$ from $T$ (the tree component of the result; the cost is
ignored) also satisfies the cache invariant. This includes keys that do not occur in $T$.
