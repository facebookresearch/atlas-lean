# Adiabatic pressure ratio from the volume ratio

Reversible adiabatic invariant in ratio form: `p₂ / p₁ = (V₁ / V₂) ^ γ` for the ideal gas
`idealGasP n R`. The relation `had`, which `adiabatic_path_integrated` gives with `nR = n * R`,
and `γ - 1 = n * R / Cv` carry the gas's own coefficient `n * R`. It needs only `Cv ≠ 0`; the
physical case is `0 < Cv`.
