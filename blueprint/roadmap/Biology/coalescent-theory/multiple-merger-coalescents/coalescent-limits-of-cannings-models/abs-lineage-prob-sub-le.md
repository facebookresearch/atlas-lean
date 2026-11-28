# One-generation estimate for the lineage count

For a [Cannings model](../cannings-models/cannings-model.md) of a population of size `N`, whose
law is exchangeable in the children, and `a < b ≤ N`, with `k = b + 1 - a`, the
[probability](../cannings-models/lineage-prob.md) `P_{b,a}` that `b` lineages have `a` parents
satisfies `|P_{b,a} - C(b, k) A(b, k)| ≤ (C(b, k) + 1) b⁴ D`, where `A` is the
[alternating sum](alt-merge-sum.md) and `D` the
[probability of a simultaneous double merger](../cannings-models/double-merge-prob.md). The
comparison term `C(b, k) A(b, k)` is the expected number of `k`-element sets of sampled lineages
that form a whole parent family (they share a parent that no other sampled lineage has). It is a
single-merger approximation, not the probability that exactly one `k`-merger occurs: other
families may form at the same time, and it can exceed `1`. For example, if the `N = 4` children
always fall into two families of two, then for `b = 4` and `a = 3`, `C(4, 2) A(4, 2) = 2`, while
`P_{4,3} = 0`. For `a = 0`, `k = b + 1` and `C(b, k) = 0`.
