# f4 is unchanged by a common symmetric difference of all lineages

Let `M` and `M'` be [drift models](../patterson-s-f-statistics/drift-model.md) with the same
populations and edges, possibly on different measure spaces, both with
[binary loadings](../patterson-s-f-statistics/has-binary-loadings.md) (every lineage weight is `0`
or `1`) and with the same drift lengths. Suppose that there is a set `R` of edges such that the
[lineage](../patterson-s-f-statistics/lineage.md) of every population `X`, its set of edges of
weight `1`, changes by `R`: `L'(X) = L(X) ∆ R`, the symmetric difference. Then the two models give
the same value of the [f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A, B; C, D)` for all
populations `A, B, C, D`. This covers rerooting a tree at a vertex `v`: each root-to-`X` path is
replaced by the path from `v` to `X`, its symmetric difference with the path `R` from the old root
to `v`.
