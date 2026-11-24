# Loaded Transfer zero

At `s = 0` the loaded transfer expression is the cast of the real
loaded DC gain expression. This is an identity between the two
expressions for every parameter choice, because both use the same
division; it makes no physical claim at the singular parameters
where `1 + beta * b * A0 = 0`. The guarded signal-level statement is
`output_eq_loadedDcGain_mul_input`.
