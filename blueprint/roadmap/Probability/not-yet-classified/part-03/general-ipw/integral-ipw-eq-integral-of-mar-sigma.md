# Identification by inverse-response weighting under MAR, general covariate σ-algebra

Under a probability law, let `m ≤ mΩ` be the always-observed covariate information and
`π = P(R | m)` the response probability. If the integrable outcome `Y` is missing at random
given `m`, `P(R ∩ {Y ∈ S} | m) = π P(Y ∈ S | m)` a.e. for every measurable `S` (a set-wise
form of the conditional independence `R ⊥ Y | m`), and strong positivity `π ≥ ε > 0` holds
a.e., then the inverse-response-weighted mean `E[1_R Y / π]` (an observed-data estimand) equals
the full-data mean `E[Y]`. Proved by `condExp_indicator_ae_eq_mul_of_mar` and the general
inverse-weighting theorem `integral_ipw_eq_integral_of_mar_condExp`.
