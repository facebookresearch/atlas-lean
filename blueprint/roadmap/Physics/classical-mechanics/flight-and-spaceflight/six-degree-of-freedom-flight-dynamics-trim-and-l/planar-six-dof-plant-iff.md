# On planar motions the plant is the reduced field on the box

Let `B` be a mass distribution of mass `1`, with centre of mass `0` and inertia tensor
`diag(I_xx, I_yy, 1)` about it for some real `I_xx` and `I_yy` (pitch inertia `1` about the
principal third axis), and let `X₁`, `X₂` and `θ` be twice continuously differentiable real
functions of time. Then the [six-degree-of-freedom plant](six-dof-plant.md) of the
[planar motion](planar-motion.md) of `B`, with the
[longitudinal maps](longitudinal-maps.md), the [longitudinal state](planar-state.md)
`(x, z, θ, q) = (X₁' − 1, X₂', θ, θ')` and gravity `(0, −1, 0)`, holds at a time `t` exactly when
the state at `t` lies in the [actuator box](actuator-box.md) and its rate at `t` is the
[reduced field](reduced-field.md):

`x' = −x − x³`, `z' = −z`, `θ' = q`, `q' = −2 q − sin θ`.
