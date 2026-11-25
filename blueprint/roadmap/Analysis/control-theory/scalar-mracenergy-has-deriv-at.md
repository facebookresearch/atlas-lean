# Energy derivative for scalar model-reference adaptive control

Derivative of the scalar model-reference adaptive control
energy. With tracking error `e = x - xm`, parameter error
`a - ahat`, adaptation gain `gamma`, and energy
`V = (e ^ 2 + (a - ahat) ^ 2 / gamma) / 2`, the plant law
`x' = a * x + b * u` with feedback
`u = (-ahat * x - lam * x + r) / b`, the reference law
`xm' = -lam * xm + r`, and the adaptation law
`ahat' = gamma * (x - xm) * x` give `V' = -lam * e ^ 2` at
the point `t`.
