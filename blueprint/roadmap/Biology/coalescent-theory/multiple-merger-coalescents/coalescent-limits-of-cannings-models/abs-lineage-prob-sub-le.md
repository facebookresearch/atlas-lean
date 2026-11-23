# One-generation estimate for the lineage count

For a [Cannings model](../cannings-models/cannings-model.md) of a population of size `N`, whose
law is exchangeable in the children, and `a < b ≤ N`, with `k = b + 1 - a`, the
[probability](../cannings-models/lineage-prob.md) `P_{b,a}` that `b` lineages have `a` parents is
`C(b, k) A(b, k)` (a single `k`-merger, with the [alternating sum](alt-merge-sum.md) `A`) up to an
error of at most `(C(b, k) + 1) b⁴ D`, where `D` is the
[probability of a simultaneous double merger](../cannings-models/double-merge-prob.md):
`|P_{b,a} - C(b, k) A(b, k)| ≤ (C(b, k) + 1) b⁴ D`.
