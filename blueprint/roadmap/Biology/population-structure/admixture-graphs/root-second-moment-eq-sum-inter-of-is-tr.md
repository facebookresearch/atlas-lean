# Root-relative second moment on a tree is the shared lineage length

Let `G` be an [admixture graph](admixture-graph.md) on a finite set of nodes that is a
[tree](is-tree.md), and let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on
the [edges](edge.md) of `G` with drift lengths `ℓ` whose lineage weights are the
[lineage weights](weight.md) of `G`. Then for all nodes `X`, `Y` the
[root-relative second moment](../patterson-s-f-statistics/root-second-moment.md) is
`Σ(X, Y) = ∑ e ∈ L X ∩ L Y, ℓ e`, the total drift length of the edges in both
[lineages](../patterson-s-f-statistics/lineage.md) `L X` and `L Y`: the edges of lineage weight `1`,
here the edges of the root-to-`X` and root-to-`Y` paths.
