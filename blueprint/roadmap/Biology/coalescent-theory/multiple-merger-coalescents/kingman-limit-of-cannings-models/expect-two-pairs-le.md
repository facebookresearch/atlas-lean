# Bound for two different pairs of lineages coalescing together

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`. Let `b` lineages sit at distinct children
`e(0), …, e(b - 1)`, and let `(k, l) ≠ (k', l')` be two
[pairs](../../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) of
lineage labels with `k < l` and `k' < l'`. The probability that `f(e(k)) = f(e(l))` and
`f(e(k')) = f(e(l'))` is at most `p_3 + D`, the sum of the
[triple-coalescence probability](triple-coalescence.md) `p_3 = N μ_3 / (N)_3` and the
[double-merger bound](double-bound.md) `D = E[X²] / (N)_4`, with `μ_3` the third
[factorial moment](factorial-moment.md) of the offspring numbers, `X` the
[pair count](pair-count.md) of the parent map, `(N)_3 = N (N - 1) (N - 2)` and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`. Here `N ≥ 3`, since two different pairs involve at least three
lineages at distinct children; for `N = 3`, `D = 0` because `(N)_4 = 0` and `x / 0 = 0`.
