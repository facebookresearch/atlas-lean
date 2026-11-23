# Log-det rate estimate

Let `ι` be a finite set of states. For a real `ι × ι` matrix `F` with
[log-det generator](log-generator.md) `G(F)` and [log-det distance](log-det-distance.md) `Δ(F)`, the
log-det rate estimate is `R(F) = Δ(F)⁻¹ · G(F)`, the log-det generator divided by the log-det
distance. With the convention `0⁻¹ = 0` it is the zero matrix when `Δ(F) = 0`. Its trace is `-1`
when every base-frequency estimate is positive and `Δ(F) ≠ 0`
([trace normalization](trace-rate-estimate.md)).
