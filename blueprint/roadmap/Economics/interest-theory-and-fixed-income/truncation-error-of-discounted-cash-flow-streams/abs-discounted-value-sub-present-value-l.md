# Truncation error bound, present-value form

Let `0 ≤ β < 1` and let the rewards be bounded, `|r_t| ≤ M` for every `t ≥ 0`. Then for every
`T` the present value `∑_{t=0}^{T-1} βᵗ r_t` of the first `T` rewards is within
`M βᵀ / (1 - β)` of the discounted value `∑_{t=0}^{∞} βᵗ r_t`, a convergent series under these
hypotheses: `|∑_{t=0}^{∞} βᵗ r_t - ∑_{t=0}^{T-1} βᵗ r_t| ≤ M βᵀ / (1 - β)`.
