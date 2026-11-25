# A ghost source with contrasts in the sampled span is absorbed exactly

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with
lineage weights `w`, and take the f4 statistics of its
[population frequencies](../patterson-s-f-statistics/freq.md). Let `T` and `G` be populations,
`S 0, …, S k` the sampled sources, `R 0, …, R r` right populations, `α` a real number and
`c 1, …, c k` real coefficients. Suppose that on every edge seen by the right set the target has the
weights of the mixture `α G + (1 - α) S 0`, that is
`(w T e - (α w G e + (1 - α) w (S 0) e)) * (w (R j) e - w (R 0) e) = 0` for every edge `e` and every
`j`, and that the right contrasts of `G` (in the intended use a source that is not sampled) are the
combination `c` of those of the sampled sources:
`f4(G, S 0; R j, R 0) = ∑ l, c l * f4(S l, S 0; R j, R 0)` for `1 ≤ j ≤ r`. Then the weights
`(α c 1, …, α c k)` solve the system `A v = b` of the [source matrix](qp-adm-source-matrix.md) `A`
and the [target vector](qp-adm-target-vector.md) `b` of `T`, whatever the signs and sizes of `α` and
`c`.
