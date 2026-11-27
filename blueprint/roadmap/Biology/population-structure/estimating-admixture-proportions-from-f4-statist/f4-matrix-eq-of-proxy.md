# Proxy left populations give the same f4 matrix as those they match

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with
lineage weights `w`, and take the f4 statistics of its
[population frequencies](../patterson-s-f-statistics/freq.md). Let `L 0, …, L n` and `L' 0, …, L' n`
be left populations and `R 0, …, R r` right populations. Suppose that each `L' i` has the lineage
weights of `L i` on every edge seen by the right set:
`(w (L' i) e - w (L i) e) * (w (R j) e - w (R 0) e) = 0` for every `i`, every edge `e` and every
`j`. Then the [qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) of `L'`
against `R`, with entries `f4(L' i, L' 0; R j, R 0)` for `1 ≤ i ≤ n` and `1 ≤ j ≤ r`, equals that of
`L` against `R`.
