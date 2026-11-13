# The defective renewal equation for the walk maximum

**The defective renewal equation for the walk maximum** (finite horizon): for `t > 0`,
`P(max_{j ≤ n} S_j ≥ t) = ∑_{k ≤ n} E[P_{n-k}(max ≥ t - H); τ₊ = k]`, where `H` is the ladder
height. The tail of the maximum is determined by the ladder-height distribution
`P(τ₊ = k, H ∈ ·) = scoreProb q f k (fun u => IsFirstLadder u ∧ u.sum ∈ ·)`.
