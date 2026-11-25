# Trace normalization of the rate estimate

Let `ι` be a finite set of states. Let `F` be a real `ι × ι` matrix whose
[base-frequency estimates](base-freq.md) `b(F) i = (∑_j F i j + ∑_j F j i) / 2` are all positive and
whose [log-det distance](log-det-distance.md) `Δ(F)` is nonzero. Then the
[log-det rate estimate](rate-estimate.md) `R(F)` has trace `tr R(F) = -1`. The second hypothesis is
needed: at `Δ(F) = 0` the estimate is the zero matrix, by the convention `0⁻¹ = 0`, and has trace
`0`.
