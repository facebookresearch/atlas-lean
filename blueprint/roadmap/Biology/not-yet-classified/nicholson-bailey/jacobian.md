# Jacobian

The Jacobian matrix of `step r a c` at `x = (H, P)`, in the ordered host and parasitoid
coordinates: with `e = exp(-a P)`,
`jacobian r a c x = [[r e, -r a H e], [c (1 - e), a c H e]]` (rows are the host and parasitoid
components, columns the derivatives in `H` and `P`). It is defined for all real `r`, `a`, `c` and
all `x`, and is the derivative of `step r a c` at every point (`hasFDerivAt_step`).
