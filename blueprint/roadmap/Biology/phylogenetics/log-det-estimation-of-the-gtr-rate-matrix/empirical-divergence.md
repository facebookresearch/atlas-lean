# Empirical divergence matrix

Let `ι` be a set of states. For aligned site pairs `X 0, X 1, …`, maps from a set `Ω` to `ι × ι`,
the empirical divergence matrix of the first `n` pairs at `ω` is the matrix of their
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md):
`F̂ₙ(ω) i j = n⁻¹ · #{k < n : X k ω = (i, j)}`. With the convention `0⁻¹ = 0` it is the zero matrix
at `n = 0`.
