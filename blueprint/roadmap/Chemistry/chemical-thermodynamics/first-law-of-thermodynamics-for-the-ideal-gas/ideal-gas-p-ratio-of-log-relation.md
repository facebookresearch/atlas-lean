# Ideal Gas P ratio of log relation

Pressure ratio of the ideal-gas model `idealGasP n R` between two states related by
`Cv * log (T₂ / T₁) + k * log (V₂ / V₁) = 0` with `γ - 1 = k / Cv`, for an arbitrary
coefficient `k`: `p₂ / p₁ = (V₁ / V₂) ^ γ`. This is an algebraic identity, not the physical
adiabat: `n * R` cancels from the pressure ratio, so `k` need not be the `n * R` of the
pressure model. The physical statement, with `k = n * R`, is `adiabatic_invariant_ratio_p`.
