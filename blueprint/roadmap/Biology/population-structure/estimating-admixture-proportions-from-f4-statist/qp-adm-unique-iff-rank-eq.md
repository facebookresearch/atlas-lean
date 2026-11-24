# A solution is unique iff the source matrix has full column rank

Let `μ` be a measure, `p X` real allele frequencies of the populations, `T` a target, `S 0, …, S k`
sources and `R 0, …, R r` right populations, with [source matrix](qp-adm-source-matrix.md) `A` (an
`r × k` matrix) and [target vector](qp-adm-target-vector.md) `b`. Suppose that `w ∈ ℝ^k` solves
`A w = b`. Then `w` is the only `v ∈ ℝ^k` with `A v = b` if and only if `A` has rank `k`, that is,
full column rank.
