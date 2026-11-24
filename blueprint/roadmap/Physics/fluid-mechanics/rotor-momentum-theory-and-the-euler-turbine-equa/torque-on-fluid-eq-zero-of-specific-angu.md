# Equal r c_θ at both ports gives zero torque, power and shaft power

Let finitely many forces `F_k` (indexed by a finite set), exerted on the fluid at points `x_k` of a
rotor turning at the signed angular speed `ω` about the shaft axis through `o`, exert the rotor
torque on the fluid, with no other external axial moment. Let an inlet and an outlet
[port](rotor-port.md) (radii `r₁`, `r₂`, swirls `c_θ₁`, `c_θ₂`) and a real `ṁ` satisfy the steady
lumped balances: the [lumped mass flows](lumped-mass-flow.md) are `-ṁ` at the inlet and `ṁ` at the
outlet, and the [axial torque](axial-torque.md) `τ` of the forces equals the sum of the
[lumped axial angular-momentum fluxes](axial-moment-flux.md) of the two ports about `o`. Let the
rotor turn steadily without bearing torque, so that the axial torques on it balance,
`τ_shaft + τ_reaction = 0`, and let the fluid react on the rotor with `τ_reaction = -τ`. If the two
ports carry the same specific axial angular momentum (axial angular momentum per unit mass),
`r₁ c_θ₁ = r₂ c_θ₂`, then the axial torque `τ` of the forces and their [power](rotor-power.md) on
the fluid vanish, and so does the engineering shaft power out `W_out = -ω τ_shaft`, the negative of
the power of the shaft torque on the rotor, for every real `ṁ` and `ω`. The swirl velocities
themselves may differ: only `r c_θ` enters.
