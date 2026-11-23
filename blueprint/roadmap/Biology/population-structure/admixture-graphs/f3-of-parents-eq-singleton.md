# Drift on the edge to a single parent adds its length to f3

Let `G` be an [admixture graph](admixture-graph.md) on a finite set of nodes, with parent sets `pa`
and admixture proportions `a`, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on the [edges](edge.md) of `G` whose
lineage weights are the [lineage weights](weight.md) of `G`; write `ℓ(c, p)` for the drift length of
the edge `(c, p)`. Let `Y` be a node with `pa(Y) = {X}`, and let `A`, `B` be parents of `X`, not
necessarily distinct. Then the drift on the edge `(Y, X)` adds its length to the
[f3 statistic](../patterson-s-f-statistics/f3.md) of the population frequencies of `M`:
`f3(Y; A, B) = f3(X; A, B) + ℓ(Y, X)`.
