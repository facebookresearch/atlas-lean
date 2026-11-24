# Rotation matrix of a change of plane axes

For `θ ∈ ℝ`, the axis-rotation matrix is `Q(θ) = [[cos θ, sin θ], [-sin θ, cos θ]]`, with rows
`(cos θ, sin θ)` and `(-sin θ, cos θ)`. It is the transpose `R(θ)ᵀ = R(-θ)` of the
[rotation matrix](../../../LinearAlgebra/special-matrices/rotation-matrices/real-planar-rotation-matrices.md)
`R(θ)` through the angle `θ`. Its rows are the unit vectors of the axes `x'`, `y'` obtained by
turning the `x`- and `y`-axes through `θ`, from `x` towards `y`. So `Q(θ)` converts the components
of a vector in the `x, y` axes into its components in the `x', y'` axes (a passive change of axes);
as a map of the plane it is the rotation through `-θ`. With this matrix the components of a plane
stress in the new axes are `Q(θ) σ Q(θ)ᵀ` ([rotated stress](rotated-stress2.md)).
