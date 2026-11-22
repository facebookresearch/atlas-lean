# Isothermal Work On

Reversible isothermal work done on `n` moles of ideal gas at temperature `T` taken from
volume `V₁` to `V₂`: `w = -(n * R * T * log (V₂ / V₁))`. Physical volumes are positive; for
`V₁ ≤ 0` or `V₂ ≤ 0`, `Real.log` returns `log |V₂ / V₁|` (and `0` at `0`), a meaningless value,
and `isothermal_work` assumes `0 < V₁` and `0 < V₂`.
