# Without return flow the peripheral amount after a bolus is nonnegative

For rates `k10 ≥ 0`, `k12 ≥ 0` and `k21 ≥ 0`, a dose `D ≥ 0` and a time `a ≥ 0`, the Duhamel
integral `∫₀ᵃ exp (-k21 * (a - s)) * (k12 * (D * exp (-(k10 + k12) * s))) ds` is nonnegative: the
mass transferred in is nonnegative and decays without sign change.

The integral is the peripheral amount at time `a` of a two-compartment model without return flow,
after a bolus `D` into the central compartment: the central compartment loses its content at the
rates `k10` (elimination) and `k12` (transfer to the peripheral compartment), so its amount is
`D * exp (-(k10 + k12) * s)`, and the peripheral compartment loses its content at the rate `k21` to
outside the system. In the [two-compartment model](pk2-generator.md), where `k21` is the transfer
back to the central compartment, the central amount is not `D * exp (-(k10 + k12) * s)` when
`D > 0`, `k12 > 0` and `k21 > 0`, and the integral is then not the peripheral amount of that model.
