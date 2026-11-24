# Discretized Biot consolidation

Finite poroelastic port-energy identity, with distinct
displacement and pressure index types. Along differentiable
trajectories `u` (displacement, `m` coordinates) and `p`
(pressure, `n` coordinates) with supplied derivative functions
satisfying, at every time, `K*u - Q*p = f` and
`C*p' + Qᵀ*u' + H*p = s`, for constant symmetric storage
matrices `K` (`m × m`) and `C` (`n × n`) and rectangular
coupling `Q` (`m × n`), the stored quadratic energy
`1/2 * (uᵀKu + pᵀCp)` has derivative equal to input power
`u'ᵀf + pᵀs` minus dissipation `pᵀHp`. The opposite signs of
the two coupling terms are essential. Reading the quadratic
forms as energy and dissipation uses the usual positivity of
the physical model; the identity itself needs only symmetry.
