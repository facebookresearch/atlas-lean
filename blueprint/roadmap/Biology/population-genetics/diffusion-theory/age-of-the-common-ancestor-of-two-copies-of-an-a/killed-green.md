# Killed Green

The Green's function `G_C` of the Wright-Fisher diffusion killed at rate `1 / x`
(coalescence of two allele copies), Patterson's Theorem 4: for `x ≤ y`,

`G_C(x, y) = -2 (x² + 2x log (1 - x) - 2x - 2 log (1 - x)) / (y² x)`,

and for `x > y`,

`G_C(x, y) = 2 (1 - x) (2y - y² + 2 log (1 - y) - 2y log (1 - y)) / ((1 - y) y² x)`.

In the diffusion reading (not formalized here), `G_C(x, y) = ∫₀^∞ C(x, y; t) dt` for
the killed transition density `C` of his Equation 4, with `y` the present-day
frequency and `x` the frequency backward in time. The branches are
`2 a₁(x) / y²` and `2 a₁(y) a₂(x) / ((1 - y) y)` (`killedGreen_eq_aux_left`,
`killedGreen_eq_aux_right`). The formula is meaningful for `x, y ∈ (0, 1)`; outside
that range Lean's totalized division takes over.
