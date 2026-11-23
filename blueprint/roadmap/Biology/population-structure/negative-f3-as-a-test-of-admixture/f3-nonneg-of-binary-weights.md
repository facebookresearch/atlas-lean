# F3 nonneg of binary weights

On an admixture graph, a target `C` whose lineage weights are all `0` or
`1` has `f3 C A B ≥ 0` for arbitrary, possibly admixed, sources `A` and `B`,
in any drift model carrying the graph's weights. Graph weights always lie
in `[0, 1]` (`AdmixtureGraph.weight_nonneg`,
`AdmixtureGraph.weight_le_one`). Binarity of `C`'s weights is assumed
directly; characterizing it by a unique root-ward path is not proved here.
