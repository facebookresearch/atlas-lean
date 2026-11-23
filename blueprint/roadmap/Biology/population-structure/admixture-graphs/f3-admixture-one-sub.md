# Three-population statistic at an admixture node in terms of α alone

Let `G` be an [admixture graph](admixture-graph.md) on a finite set of nodes, with parent sets `pa`
and admixture proportions `a`, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on the [edges](edge.md) of `G` whose
lineage weights are the [lineage weights](weight.md) of `G`; write `ℓ(c, p)` for the drift length of
the edge `(c, p)`. Let `X` be a node with `pa(X) = {A, B}`, `A ≠ B`, and put `α = a(X, A)`, so that
`a(X, B) = 1 - α` by the [complementary proportions](prop-eq-one-sub-of-parents-eq-pair.md). Then
`f3(X; A, B) = α² ℓ(X, A) + (1 - α)² ℓ(X, B) - α (1 - α) f2(A, B)` for the
[f2](../patterson-s-f-statistics/f2.md) and [f3](../patterson-s-f-statistics/f3.md) statistics of
the population frequencies of `M`.
