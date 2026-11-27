# Longitudinal force and moment maps on the actuator box

The longitudinal [force and moment maps](force-moment-maps.md) have the
[actuator box](actuator-box.md) as admitted domain. At an admitted state `(x, z, θ, q)` they give
the body force

`F_B = Rz(θ)ᵀ (F_aero + A)`,

the [aerodynamic force](aero-force.md) plus the [actuator force](actuator-force.md) at
`(x, z)` in body components, with `Rz(θ)` the [pitch orientation](pitch-orientation.md), and the
body moment `(0, 0, M)` about the pitch axis, with `M = −2 q − sin θ` the
[pitch-moment actuator](pitch-moment.md).
