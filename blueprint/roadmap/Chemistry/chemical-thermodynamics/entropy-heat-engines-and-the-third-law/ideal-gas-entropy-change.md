# Ideal-gas entropy change for constant heat capacity

The integrated ideal-gas entropy change `ΔS = n * cv * log (T₂ / T₁) + n * R * log (V₂ / V₁)` with
constant molar heat capacity `cv`: the integral of the model differential
`dS = n * cv * dT / T + n * R * dV / V`, which is a model input. Domain: positive temperatures and
volumes. At `T₁ = 0` or `V₁ = 0` the conventions `x / 0 = 0` and `log 0 = 0` give a meaningless
value (with constant `cv`, heating from `T₁ → 0` has a divergent `ΔS`, yet `T₁ = 0` gives a finite
value), and a negative ratio gives `log (-x) = log x`.
