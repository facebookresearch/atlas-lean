# Upwind weights in the unit interval keep concentrations nonnegative

On two periodic cells, the upwind tracer update with weight `ν` takes concentrations `c₁`, `c₂` to
`c₁' = (1 - ν) * c₁ + ν * c₂` and `c₂' = (1 - ν) * c₂ + ν * c₁`. If `0 ≤ ν ≤ 1` and
`c₁, c₂ ≥ 0`, then `c₁' ≥ 0` and `c₂' ≥ 0`.
