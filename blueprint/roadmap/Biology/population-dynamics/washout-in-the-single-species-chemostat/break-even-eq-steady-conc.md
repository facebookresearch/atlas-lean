# The break-even concentration is the chemostat model's steady substrate level

For
`D ≠ 0`, the break-even concentration `λ = a / (m / D - 1)` equals
`steadyConc m a D = D a / (m - D)`, the substrate level of the interior steady state
`interiorState` of the chemostat model `Domains.Biology.Dynamics.Chemostat`; for `m > 0`, `a > 0`
and `D < m`, the Monod growth rate `m S / (a + S)` equals `D` there.
