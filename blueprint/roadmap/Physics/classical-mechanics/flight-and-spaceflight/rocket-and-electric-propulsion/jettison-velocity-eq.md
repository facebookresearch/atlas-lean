# Jettison velocity eq

A jettison with zero relative velocity leaves the velocity unchanged: a vehicle of mass `m₁` at
velocity `v` drops the mass `m₁ - m₂`, which keeps the velocity `v`, and the remaining mass `m₂`
moves at `w`. If `m₂ ≠ 0` (a positive remaining mass in the model), momentum is conserved,
`m₂ w + (m₁ - m₂) v = m₁ v`, exactly when `w = v`. The identity needs only `m₂ ≠ 0`; a jettison
is the case `m₂ ≤ m₁`, which `staged_velocity_increment` requires of every transition.
