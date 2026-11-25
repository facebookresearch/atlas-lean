# A constant density k on a measurable face has flux area times k

For parameter domains `D_f ⊆ ℝ²` and densities `j_f : ℝ² → ℝ` indexed by the six faces
`f = 0, …, 5`, the [flux through face `f`](face-flux.md) is `Φ_f = ∫_{D_f} j_f(p) dp`. If `D_f` is
measurable and `j_f = k` on `D_f`, then

`Φ_f = |D_f| k`,

where `|D_f|` is the area of `D_f`, read as `0` when it is infinite. For a face of infinite area
both sides are therefore `0` (the constant is not integrable when `k ≠ 0`); for a face of
[finite area](face-flux-of-const-of-measure-ne-top.md) the flux is a genuine integral.
