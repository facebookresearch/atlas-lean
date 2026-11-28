# Entry of a finite CT design matrix

For a family of basis functions `phi : ι → ℝ² → ℝ` (on the Euclidean plane),
a direction `xi ∈ ℝ²`, a level `p : ℝ` and an index `i`, the CT design entry
is the Euclidean Radon transform of `phi i` at `(xi, p)`: the integral of
`phi i` over the level set `{y | ⟪y, xi⟫ = p}` with respect to one-dimensional
Hausdorff measure. For `xi ≠ 0` the level set is a line; for `xi = 0` it is the
whole plane when `p = 0` and empty otherwise. No normalization `‖xi‖ = 1` is
assumed; for a unit direction `xi`, `p` is the signed distance of the line from
the origin.
