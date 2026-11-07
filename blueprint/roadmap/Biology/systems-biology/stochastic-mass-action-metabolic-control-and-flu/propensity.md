# Stochastic mass-action propensity

The stochastic mass-action propensity of reaction `r` in state `x` (molecule counts):
`k r * ∏_s x_s (x_s - 1) ⋯ (x_s - src_s + 1)`, the falling factorial
`Nat.descFactorial x_s src_s` (it vanishes when `x_s < src_s`). Anderson, Craciun & Kurtz
(2010), §2.
