# Concentration in the one-compartment model

For a clearance `CL`, a volume `V`, an infusion rate `R` and an initial amount `A₀` (real numbers),
the concentration at time `t` is `C(t) = A(t) / V`, where `A(t)` is the amount
`A₀ * exp (-k * t) + ∫₀ᵗ exp (-k * (t - s)) * R ds` with the [elimination rate](elim-rate.md)
`k = CL / V`. It is defined for all real inputs; with the convention `x / 0 = 0` it is `0` when
`V = 0`. In the model `V > 0` and `CL ≥ 0`.
