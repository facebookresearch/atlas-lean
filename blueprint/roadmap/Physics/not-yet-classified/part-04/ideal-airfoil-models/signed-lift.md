# Signed Lift

Signed lift per unit span extracted from a complex force
`C = Fx - I * Fy` at incidence `α`.

The free-stream direction is `(cos α, sin α)`, and positive lift is
the component in the counterclockwise normal direction
`(-sin α, cos α)`. In coordinates this component is
`-(sin α * C.re + cos α * C.im)`, equivalently
`-(exp (α * I) * C).im`. At `α = 0` it is `Fy`.
