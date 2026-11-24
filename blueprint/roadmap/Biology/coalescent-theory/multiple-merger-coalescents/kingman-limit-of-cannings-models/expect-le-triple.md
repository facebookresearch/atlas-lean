# Bound for events that force three children to share a parent

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`, and let `x, y, z` be three distinct
children. For every event `Q` on parent maps such that `Q(f)` implies `f x = f y = f z`, the
probability of `Q` is at most the [triple-coalescence probability](triple-coalescence.md)
`N μ_3 / (N)_3`, where `μ_3 = (1/N) ∑_j E[ν_j (ν_j - 1) (ν_j - 2)]`, `ν_j` is the number of children
of parent `j` and `(N)_3 = N (N - 1) (N - 2)`.
