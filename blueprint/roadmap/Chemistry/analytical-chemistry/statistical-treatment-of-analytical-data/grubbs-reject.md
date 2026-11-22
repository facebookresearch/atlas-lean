# Grubbs' test rejection rule

Grubbs' test at a critical value `gcrit ≥ 0` rejects the most extreme observation of a sample `x`
of `n ≥ 3` observations when Grubbs' statistic `G` exceeds `gcrit`: the rule is `n ≥ 3`,
`0 ≤ gcrit` and `gcrit < G`, so at `G = gcrit` it does not reject. The test is not defined for
fewer than three observations, which are [never rejected](not-grubbs-reject-of-lt-three.md). The
critical value is an explicit nonnegative input (tabulated values assume normality); a negative
`gcrit` never rejects.
