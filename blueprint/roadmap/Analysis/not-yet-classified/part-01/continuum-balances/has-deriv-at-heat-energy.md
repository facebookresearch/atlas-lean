# Energy identity

**Energy identity** (MF08.4): if `u` is jointly `C²`, solves `∂ₜu = D ∂ₓₓu` on `[0, L]` at
time `t` and vanishes at `x = 0` and `x = L` at time `t`, then
`E'(t) = -2D ∫₀ᴸ (∂ₓu)²`. The proof applies `hasDerivAt_integral_of_localConservation` to the
density `u²`, the flux `-2D u ∂ₓu` and the source `-2D (∂ₓu)²`; the boundary terms vanish by
the Dirichlet condition.
