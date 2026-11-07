# Bhaskar–Song identifiability

**Bhaskar–Song identifiability** (Bhaskar & Song 2014, Corollary 7, "determined" half,
stated for the first-coalescence times): two piecewise-constant histories with `K` pieces whose
expected first-coalescence times `c_m` agree for `2 ≤ m ≤ n`, with `n ≥ 2K`, have the same
population size at every time `s ≥ 0`. The proof writes `C(m,2) c_m` as an exponential sum in
`C(m,2)` over at most `2K - 1` rates (`choose_two_mul_firstCoalMean`), identifies the
coefficients with `Real.eq_zero_of_sum_mul_exp_eq_zero`, recovers the size as a function of
coalescent time (the `dual` history) and inverts `R` (`cumRate_dual_cumRate`).
