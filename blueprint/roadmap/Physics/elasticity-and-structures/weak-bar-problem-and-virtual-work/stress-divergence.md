# Divergence of a stress field

For a matrix field `σ : ℝ³ → ℝ^{3×3}` and a point `x`, the stress divergence is the vector with
components `(div σ)_i(x) = ∑_j ∂_j σ_ij(x)`, the [divergence](../../../Probability/stochastic-calculus/fokker-planck-equation/divergence.md) of the `i`-th row; each partial
derivative is the Fréchet derivative applied to `e_j`, taken to be `0` where the component is not
differentiable.
