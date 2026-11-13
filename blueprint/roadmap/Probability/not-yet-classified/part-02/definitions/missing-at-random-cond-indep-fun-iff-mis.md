# The two named MAR predicates agree

For a real outcome and a countably valued covariate
with measurable singletons, `MissingAtRandomCondIndepFun` (Mathlib's `CondIndepFun` given `σ(X)`)
holds iff the discrete-covariate predicate `MissingOutcomes.MissingAtRandom` of the AIPW
development does. Note the argument orders: `R X hX Y` here, `R Y X` there.
