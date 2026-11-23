# A source descended from the target fits it, with f4 rank at most one

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with
lineage weights `w`, and take the f4 statistics of its
[population frequencies](../patterson-s-f-statistics/freq.md). Let `T`, `S₀` and `S₁` be
populations, `R 0, …, R r` right populations and `β ≠ 0` a real number. Suppose that the source `S₁`
descends from the target: on every edge seen by the right set it has the weights of the mixture
`β T + (1 - β) S₀`, that is `(w S₁ e - (β w T e + (1 - β) w S₀ e)) * (w (R j) e - w (R 0) e) = 0`
for every edge `e` and every `j` (drift of `S₁` on edges that no right contrast sees is allowed).
Then, for the sources `(S₀, S₁)` with reference `S₀`, the weight `1 / β` on `S₁` solves the system
of the [source matrix](qp-adm-source-matrix.md) and the [target vector](qp-adm-target-vector.md) of
`T`, and the [qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) of the left
populations `(S₀, T, S₁)`, with reference `S₀`, against `R` has rank at most one.
