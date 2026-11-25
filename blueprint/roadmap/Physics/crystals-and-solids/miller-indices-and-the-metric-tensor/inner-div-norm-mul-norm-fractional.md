# Normalized inner product with its numerator from the metric tensor

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`, with [metric tensor](metric-tensor.md)
`G`, `G_ij = a_i · a_j`. For all real `v`, `w ∈ ℝ³` and `x = Σ_i v_i a_i`, `y = Σ_j w_j a_j`,

`(x · y) / (‖x‖ ‖y‖) = (Σ_ij v_i G_ij w_j) / (‖x‖ ‖y‖)`.

When `x` or `y` is `0`, both sides are `0` by the convention `t / 0 = 0`. The norms in the
denominator are left as they are; the [angle formula](cos-angle-fractional.md) expresses them
through `G` too.
