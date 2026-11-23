# Least-squares formula for the weights under full column rank

Let `μ` be a measure, `p X` real allele frequencies of the populations, `T` a target, `S 0, …, S k`
sources and `R 0, …, R r` right populations, with [source matrix](qp-adm-source-matrix.md) `A` (an
`r × k` matrix) and [target vector](qp-adm-target-vector.md) `b`. If `w ∈ ℝ^k` solves `A w = b` and
`A` has rank `k`, then `w = (Aᵀ A)⁻¹ Aᵀ b`, the ordinary least-squares (normal-equation) formula.
Full column rank makes `Aᵀ A` invertible, so the inverse is the ordinary one.
