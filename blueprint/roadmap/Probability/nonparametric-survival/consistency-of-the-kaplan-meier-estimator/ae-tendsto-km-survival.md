# Consistency of the Kaplan–Meier estimator at a grid time

Let the subjects
`Zᵢ = (Tᵢ, Cᵢ)` be independent with the independent censoring law `indepLaw pT pC` (the product
of the law `pT` of `T` and the law `pC` of `C`). If the observed at-risk mass `P(min T C ≥ m)`
is nonzero, then almost surely the Kaplan–Meier estimate at time `m` converges to
`∏_{j ≤ m} (1 - h(j))`, where `h` is the hazard of `T`; by `prod_one_sub_hazard` this is
`P(T > m)` (`ae_tendsto_kmSurvival_survival`). This is consistency for the survival function of
`T` at grid points only.
