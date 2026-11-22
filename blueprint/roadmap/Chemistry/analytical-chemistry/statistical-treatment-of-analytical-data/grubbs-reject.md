# Grubbs Reject

Grubbs decision procedure: reject the most extreme observation of a sample `x` of `n ≥ 3`
observations at the critical value `gcrit ≥ 0`. The test is not defined for fewer than three
observations, which are never rejected (`not_grubbsReject_of_lt_three`). The critical value is an
explicit nonnegative input (tabulated values assume normality); a negative `gcrit` never
rejects.
