# The `k`-th cross-diagonal dependence coefficient

**The `k`-th cross-diagonal dependence coefficient** `Δ_k = S_k - e_k(p)`: the excess of the
`k`-th factorial moment of the number of exceeding diagonals over its value `e_k(p)` for
independent diagonals with the same marginals. `crossDep_eq_sum`: it is the sum over `k`-sets
`T` of diagonals of `P(⋂_{d ∈ T} {M_d > t}) - ∏_{d ∈ T} P(M_d > t)`. It vanishes for `k ≤ 1`
(`crossDep_zero`, `crossDep_one`), and the terms of letter-disjoint pairs vanish
(`twoProb_diag_and_diag_of_disjoint`); the diagonals are not independent in general, so for
`k ≥ 2` nothing forces it to vanish (it does vanish for the degenerate zero score, `crossDep_s0`
in the test file).
