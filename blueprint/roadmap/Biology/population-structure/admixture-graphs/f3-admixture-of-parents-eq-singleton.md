# Three-population statistic of an admixture followed by private drift

Let `G` be an [admixture graph](admixture-graph.md) on a finite set of nodes, with parent sets `pa`
and admixture proportions `a`, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on the [edges](edge.md) of `G` whose
lineage weights are the [lineage weights](weight.md) of `G`; write `ℓ(c, p)` for the drift length of
the edge `(c, p)`. Let `X` be a node with `pa(X) = {A, B}`, `A ≠ B`, put `α = a(X, A)`, and let `Y`
be a node with `pa(Y) = {X}`. Then
`f3(Y; A, B) = α² ℓ(X, A) + (1 - α)² ℓ(X, B) - α (1 - α) f2(A, B) + ℓ(Y, X)` for the
[f2](../patterson-s-f-statistics/f2.md) and [f3](../patterson-s-f-statistics/f3.md) statistics of
the population frequencies of `M`: the [admixture formula at `X`](f3-admixture.md) plus the
drift on the edge `(Y, X)`.
