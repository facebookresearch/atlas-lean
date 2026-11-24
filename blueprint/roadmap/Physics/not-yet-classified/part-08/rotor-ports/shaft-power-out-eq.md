# Shaft power out is the negative of the power on the fluid

Model inputs: the rotor torque
on the fluid is exerted by forces `F k` at points `x k` moving with the rotor, with the steady
lumped balances of `powerOnFluid_eq`; the rotor turns steadily, so the axial torques on it balance,
`τ_shaft + τ_reaction = 0` (no bearing torque), and the fluid reacts on the rotor with
`τ_reaction = -τ`, `τ` the axial torque of those forces. Then the shaft torque on the rotor is
`τ`, and the engineering shaft power out `workOut (ω τ_shaft)` is minus the power of the forces on
the fluid, `ṁ (U₁ cθ₁ - U₂ cθ₂)`.
