# Array Polygon

The **polygonal process** of a triangular array in `C([0,1])`: the linear interpolation of
the partial sums `k ↦ ∑_{i < k} ξ n i` at the grid times `k / n` (`arrayPolygon_apply`). It is
Donsker's `donskerProcess` with the `1/√n` normalization undone.
