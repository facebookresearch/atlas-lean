# Coalescence probability of a Cannings model

For a [Cannings model](cannings-model.md) of a population of size `N`, the coalescence
probability `c_N = q_2` is the [probability](merge-prob.md) that two sampled lineages have the
same parent; it is `0` for `N < 2` and sets the coalescent time scale. For `N ≥ 2`,
[`c_N = E[ν_1 (ν_1 - 1)] / (N - 1)`](../coalescent-limits-of-cannings-models/merge-prob-mul-desc-factorial.md),
with `ν_1` the number of offspring of a fixed parent.
