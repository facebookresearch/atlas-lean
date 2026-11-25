# Ideal force actuator of the longitudinal fixture

For real `x` and `z`, the ideal vector force actuator of the fixture is, in inertial components,

`A = (−x − x³, 1 − z, 0) − F_aero`,

with `F_aero` the [aerodynamic force](aero-force.md) at the velocity `(1 + x, z, 0)`. It is an
explicit part of the model, chosen so that aerodynamics, actuator and weight
[add up](aero-force-add-actuator-force-add-weight.md) to `(−x − x³, −z, 0)`.
