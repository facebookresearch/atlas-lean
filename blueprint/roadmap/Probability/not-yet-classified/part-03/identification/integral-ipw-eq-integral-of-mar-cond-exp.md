# Identification by inverse-response weighting under MAR, general covariate

Let the
always-observed covariate information be a sub-σ-algebra `m` and `π = P(R | m)` the response
probability. If `Y` is integrable, the outcome is mean-missing-at-random,
`E[1_R Y | m] = π E[Y | m]` (implied by `R ⊥ Y | m`), and strong positivity `π ≥ ε > 0`
holds, then `E[1_R Y / π] = E[Y]`. This is `integral_ipw_treated_condExp` with the response
event as the treatment and the missing outcome as the treated potential outcome.
