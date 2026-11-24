# Pinsker PMF

Pinsker's inequality for probability mass functions on a finite
type, with no positivity hypotheses: the squared `L1` distance is at
most twice the Kullback-Leibler divergence (in nats). The right side
is stated in `ℝ≥0∞`, so it stays correct when the divergence is
infinite (the `ENNReal.toReal` form would be false there).
