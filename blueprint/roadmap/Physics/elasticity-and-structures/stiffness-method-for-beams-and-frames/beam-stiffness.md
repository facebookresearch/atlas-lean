# Beam Stiffness

Beam-element stiffness matrix for a prismatic Euler-Bernoulli
element with flexural rigidity `EI` and length `L`, in the nodal
coordinates `(v1, θ1, v2, θ2)` (deflections and rotations at the
two ends), with the conjugate end-force sign convention:
`K = (EI / L^3)` times the classical coefficient matrix. The
definition is the totalized formula; no positivity is asserted by
the definition itself.
