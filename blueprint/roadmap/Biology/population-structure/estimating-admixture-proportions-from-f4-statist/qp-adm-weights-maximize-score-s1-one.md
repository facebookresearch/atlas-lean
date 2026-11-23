# An exact solution maximizes the unweighted least-squares score

Let `μ` be a measure, `p X` real allele frequencies of the populations, `T` a target, `S 0, …, S k`
sources and `R 0, …, R r` right populations, with [source matrix](qp-adm-source-matrix.md) `A` and
[target vector](qp-adm-target-vector.md) `b`. If `w ∈ ℝ^k` solves `A w = b`, then
`S1(A v) ≤ S1(A w)` for every `v ∈ ℝ^k`, where `S1` is the
[score S1](../fitting-admixture-graphs-by-least-squares/score-s1.md) with identity covariance
`Q = 1` and estimated statistics `b`, `S1(g) = -½ ∑ j, (g j - b j) ^ 2`. Here `S1(A w) = 0`.
