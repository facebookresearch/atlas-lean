# The f4 matrix rank is at most the rank of the right contrasts

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with
lineage weights `w`, and let `L 0, …, L n` be left and `R 0, …, R r` right populations. Then the
[qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) of `L` against `R`, for
the [population frequencies](../patterson-s-f-statistics/freq.md) of `M`, has rank at most the rank
of the [contrast matrix](contrast-matrix.md) of `R`, with entries `w (R j) e - w (R 0) e`. So a
qpWave matrix of rank `m` needs right contrasts of rank at least `m`.
