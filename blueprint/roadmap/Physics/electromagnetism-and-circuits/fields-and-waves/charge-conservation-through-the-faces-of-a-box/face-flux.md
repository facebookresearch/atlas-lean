# Flux of a face density over its parameter domain

For parameter domains `D_f ⊆ ℝ²` and densities `j_f : ℝ² → ℝ` indexed by the six faces `f = 0, …, 5`
of a box, the flux through face `f` is

`Φ_f = ∫_{D_f} j_f(p) dp`,

the [terminal current](../ohm-s-law-for-a-uniform-conductor/terminal-current.md) of `j_f` through
`D_f`, with respect to Lebesgue measure; the integral is `0` when the integrand is not integrable
there. When `j_f` is the outward-normal current density of face `f`, `Φ_f` is the outward current of
that face.
