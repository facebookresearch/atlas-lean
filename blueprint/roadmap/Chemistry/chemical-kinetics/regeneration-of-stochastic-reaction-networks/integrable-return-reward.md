# Positive recurrence from a balanced law

Under the hypotheses of
`measure_return_eq_one`, if all visits to `x₀` happen from every initial state, the mean return
time to `x₀` is finite. Otherwise the long-run fraction of time at `x₀` would vanish from every
initial state (renewal theorem with infinite mean), contradicting `eq_tsum_of_ae_tendsto`,
which identifies it with `w(x₀) > 0`.
