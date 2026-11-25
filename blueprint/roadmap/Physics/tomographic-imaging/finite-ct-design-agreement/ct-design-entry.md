# Entry of a finite CT design matrix

For a family of basis functions `phi : ι → ℝ² → ℝ` (on the Euclidean plane),
a direction `xi ∈ ℝ²`, a level `p : ℝ` and an index `i`, the CT design entry
is the Euclidean Radon transform of `phi i` at `(xi, p)`: the integral of
`phi i` over the line `{y | ⟪y, xi⟫ = p}` with respect to one-dimensional
Hausdorff measure. No normalization `‖xi‖ = 1` is assumed; with it, `p` is
the signed distance of the line from the origin.
