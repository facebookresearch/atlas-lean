# The interval-tree smart constructor preserves the cache invariant

If interval trees $L$
and $R$ satisfy the cache invariant (every cached maximum high endpoint, height and size is
exact), then for every entry $e$ the node that the smart constructor builds from $L$, $e$ and $R$
also satisfies the cache invariant.
