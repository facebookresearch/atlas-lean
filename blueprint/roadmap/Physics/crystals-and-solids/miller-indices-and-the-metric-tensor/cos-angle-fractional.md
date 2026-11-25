# Angles from the metric tensor

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`, with [metric tensor](metric-tensor.md)
`G`, `G_ij = a_i · a_j`. For all real `v`, `w ∈ ℝ³`, the angle `θ` between `x = Σ_i v_i a_i` and
`y = Σ_j w_j a_j` satisfies

`cos θ = (Σ_ij v_i G_ij w_j) / (√(Σ_ij v_i G_ij v_j) √(Σ_ij w_i G_ij w_j))`.

Here `θ ∈ [0, π]` is the unoriented angle `arccos((x · y) / (‖x‖ ‖y‖))`. When `x` or `y` is `0`, the
conventions `t / 0 = 0` and `arccos 0 = π / 2` give `θ = π / 2`, and both sides are `0`.
