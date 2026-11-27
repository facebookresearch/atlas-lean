# Trajectory succ

For any weights `T`, thresholds `U`, schedule `σ`, initial state `v₀` and index `k`, the
successor state results from the next scheduled attempt:
`trajectory T U σ v₀ (k + 1) = step T U (σ k) (trajectory T U σ v₀ k)`.
