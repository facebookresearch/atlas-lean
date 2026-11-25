# Double-merger bound of a Cannings model

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N`, the
double-merger bound is `E[X²] / (N)_4`, where `X = ∑_j ν_j (ν_j - 1)` is the
[pair count](pair-count.md) of the parent map, `E` is the expectation under its law and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`. For `N ≥ 4` it [bounds](expect-double-le.md) the probability
that two disjoint pairs of distinct children each have a common parent. For `N ≤ 3`, `(N)_4 = 0` and
the value is `0` by the convention `x / 0 = 0`.
