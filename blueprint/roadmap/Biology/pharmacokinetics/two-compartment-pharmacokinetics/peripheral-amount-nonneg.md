# Nonnegative rates and dose give a nonnegative peripheral amount

For rates `k10 ≥ 0`, `k12 ≥ 0` and `k21 ≥ 0`, a dose `D ≥ 0` and a time `a ≥ 0`, the Duhamel
integral `∫₀ᵃ exp (-k21 * (a - s)) * (k12 * (D * exp (-(k10 + k12) * s))) ds` is nonnegative. It is
the amount at time `a` of a compartment that receives `k12` times the central amount
`D * exp (-(k10 + k12) * s)` and loses its content at rate `k21`: the mass transferred in is
nonnegative and decays without sign change.
