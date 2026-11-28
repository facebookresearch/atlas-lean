# Life Annuity Value

Expected present value of payments contingent on survival. The indices `k ∈ s` label
instalments; `date k` is the actual time, which need not be an integer. A death at `date k`
earns no payment at that time. The expectation is for a measurable lifetime under a probability
measure, as in `lifeAnnuityValue_eq_sum`.
