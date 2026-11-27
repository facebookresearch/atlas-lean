# The break-even formula is the chemostat model's candidate interior substrate level

For
`D ≠ 0`, the break-even concentration `λ = a / (m / D - 1)` equals
`steadyConc m a D = D a / (m - D)`, the substrate coordinate of the candidate interior state
`interiorState` of the chemostat model `Domains.Biology.Dynamics.Chemostat`. This is an identity
of formulas: for `m > 0`, `a > 0` and `D < m` the Monod growth rate `m S / (a + S)` equals `D` at
`S = λ`, but the candidate is a steady state with positive biomass `y (S⁰ - λ)` only for
positive parameters with `D < m S⁰ / (a + S⁰)`, that is `m > D` and `λ < S⁰`, as
`equilibria_and_washout_threshold` states.
