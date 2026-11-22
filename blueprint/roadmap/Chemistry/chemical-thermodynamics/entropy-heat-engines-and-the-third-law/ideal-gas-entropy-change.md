# Ideal Gas Entropy Change

The integrated ideal-gas entropy change
`ΔS = n * cv * log (T₂ / T₁) + n * R * log (V₂ / V₁)` with constant molar heat capacity
`cv`: the integral of the model differential `dS = n * cv * dT / T + n * R * dV / V`. The
lemmas below are consequences of this definition, not a derivation of the differential from
statistics. Domain: positive temperatures and volumes. At `T₁ = 0` or `V₁ = 0`, Lean's
`x / 0 = 0` and `Real.log 0 = 0` give junk (with constant `cv`, heating from `T₁ → 0` has a
divergent `ΔS`, yet `T₁ = 0` returns a finite value), and a negative ratio meets
`Real.log (-x) = Real.log x`. The lemmas that read `ΔS` physically assume positive temperatures
and volumes; `idealGasEntropyChange_totalCV` and `idealGasEntropyChange_isothermal` only rewrite
the formula and hold on junk inputs too.
