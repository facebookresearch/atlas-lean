# Proxy sources give the same f4 system as the sources they match

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with
lineage weights `w`, and take the f4 statistics of its
[population frequencies](../patterson-s-f-statistics/freq.md). Let `T` be a target, `S 0, …, S k`
and `S' 0, …, S' k` two lists of sources and `R 0, …, R r` right populations. Suppose that each
`S' l` has the lineage weights of `S l` on every edge seen by the right set:
`(w (S' l) e - w (S l) e) * (w (R j) e - w (R 0) e) = 0` for every `0 ≤ l ≤ k`, every edge `e` and
every `j`. Then replacing `S` by `S'` leaves the [source matrix](qp-adm-source-matrix.md) and the
[target vector](qp-adm-target-vector.md) of `T` unchanged, so both lists of sources give the same
solutions, whatever the weights of the `S' l` on the other edges.
