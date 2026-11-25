# Three-population statistic at an admixture node with proportion one

Let `G` be an [admixture graph](admixture-graph.md) on a finite set of nodes, with parent sets `pa`
and admixture proportions `a`, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on the [edges](edge.md) of `G` whose
lineage weights are the [lineage weights](weight.md) of `G`; write `ℓ(c, p)` for the drift length of
the edge `(c, p)`. If `X` is a node with `pa(X) = {A, B}`, `A ≠ B` and `a(X, A) = 1`, then
`f3(X; A, B) = ℓ(X, A)` for the [f3 statistic](../patterson-s-f-statistics/f3.md) of the population
frequencies of `M`. Here `X` descends from `A` alone (`a(X, B) = 0`), and `f3` carries no admixture
signal.
