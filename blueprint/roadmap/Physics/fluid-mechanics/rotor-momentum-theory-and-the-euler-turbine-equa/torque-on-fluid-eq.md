# Euler torque τ = ṁ (r₂ c_θ₂ − r₁ c_θ₁) − M_ext from the balances

Let `o` be a point of the shaft axis, and let an inlet and an outlet [port](rotor-port.md) (radii
`r₁`, `r₂`, swirls `c_θ₁`, `c_θ₂`) and real numbers `ṁ`, `τ` and `M_ext` satisfy, as model inputs of
steady flow through a rotor control volume:

- the steady mass balance: the [lumped mass flows](lumped-mass-flow.md) are `-ṁ` at the inlet and
  `ṁ` at the outlet;
- the steady angular-momentum balance about the shaft applied to the lumped ports: `τ + M_ext`
  equals the sum of the [lumped axial angular-momentum fluxes](axial-moment-flux.md) of the two
  ports about `o`, where `τ` is the axial torque exerted on the fluid by the rotor and `M_ext` the
  sum of every other external axial moment.

Then `τ = ṁ (r₂ c_θ₂ - r₁ c_θ₁) - M_ext`. No sign of `ṁ` is assumed; for `ṁ > 0` the fluid enters at
the inlet and leaves at the outlet.
