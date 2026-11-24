# Turbine sign: for ṁ > 0, W_out > 0 exactly when U₂ c_θ₂ < U₁ c_θ₁

Let finitely many forces `F_k` (indexed by a finite set), exerted on the fluid at points `x_k` of a
rotor turning at the signed angular speed `ω` about the shaft axis through `o`, exert the rotor
torque on the fluid, with no other external axial moment. Let an inlet and an outlet
[port](rotor-port.md) (radii `r₁`, `r₂`, swirls `c_θ₁`, `c_θ₂`) and a real `ṁ` satisfy the steady
lumped balances: the [lumped mass flows](lumped-mass-flow.md) are `-ṁ` at the inlet and `ṁ` at the
outlet, and the [axial torque](axial-torque.md) `τ` of the forces equals the sum of the
[lumped axial angular-momentum fluxes](axial-moment-flux.md) of the two ports about `o`. Let the
rotor turn steadily without bearing torque, so that the axial torques on it balance,
`τ_shaft + τ_reaction = 0`, and let the fluid react on the rotor with `τ_reaction = -τ`. If moreover
`ṁ > 0`, then the engineering shaft power out `W_out = -ω τ_shaft`, the negative of the power of the
shaft torque on the rotor, is positive exactly when `U₂ c_θ₂ < U₁ c_θ₁`, and the
[power](rotor-power.md) `P` of the forces on the fluid is negative exactly when `U₂ c_θ₂ < U₁ c_θ₁`,
with the signed blade speeds `U₁ = ω r₁` and `U₂ = ω r₂`. This is the turbine regime.
