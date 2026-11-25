# Without full column rank every solution lies on a line of solutions

Let `μ` be a measure, `p X` real allele frequencies of the populations, `T` a target, `S 0, …, S k`
sources and `R 0, …, R r` right populations, with [source matrix](qp-adm-source-matrix.md) `A` (an
`r × k` matrix) and [target vector](qp-adm-target-vector.md) `b`. If `w ∈ ℝ^k` solves `A w = b` and
the rank of `A` is not `k`, then there is a nonzero `d ∈ ℝ^k` with `A (w + s d) = b` for every real
`s`. Along this line a weight `w l + s d l` with `d l ≠ 0` takes every real value.
