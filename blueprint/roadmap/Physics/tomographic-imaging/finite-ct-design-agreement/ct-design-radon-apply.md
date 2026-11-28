# Finite design application law

Let `s` be a finite set of indices, `phi : ι → ℝ² → ℝ` basis functions on
the Euclidean plane, `x : ι → ℝ` coefficients, `xi ∈ ℝ²` and `p : ℝ`. If
each `phi i` with `i ∈ s` is integrable on the level set `{y | ⟪y, xi⟫ = p}`
(a line when `xi ≠ 0`) with respect to one-dimensional Hausdorff measure, then the Euclidean Radon
transform of `∑_{i ∈ s} x i * phi i` at `(xi, p)` equals
`∑_{i ∈ s} x i * R(phi i)(xi, p)`, where `R(f)(xi, p)` is the Euclidean Radon
transform of `f` at `(xi, p)`: each coefficient multiplies the transform of its
own basis function.
