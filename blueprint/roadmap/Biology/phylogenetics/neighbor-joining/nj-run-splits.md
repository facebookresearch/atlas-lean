# Neighbor joining is exact on tree metrics

Let `d` be the path-length metric of a
binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w`. Then every complete run
of neighbor joining (stopped with at most three clusters) forms exactly the splits of the
internal edges of the tree: a set of taxa `A` or its complement is a formed cluster if and
only if `A` is the set of taxa on the `a`-side of an edge `{a, b}` with both endpoints
internal.

## Sources

- Saitou & Nei (1987); Studier & Keppler (1988); Gascuel (1994); Bryant (2005). Proves the deferred entry `njRun_splits`.
