# GTR divergence law on site pairs

Let `ι` be a finite set of states. For real base frequencies `π`, exchangeabilities `s` and a branch
length `t` with [divergence weight](../identifiability-of-the-gtr-model/gtr-pair-law.md) `w(i, j) = π i · exp (t · Q) i j`, the GTR
divergence law is the measure `μ = ∑_a max (w(a), 0) · δ_a` on site pairs `a ∈ ι × ι`, a point mass
at each pair. It is defined for all real parameters: a negative weight is clamped to `0`, so it puts
no mass at its pair. It is a probability measure when `π i ≥ 0`, `∑_i π i = 1`, `s i j ≥ 0` for
`i ≠ j` and `t ≥ 0`.
