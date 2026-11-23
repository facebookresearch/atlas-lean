# Gaussian projection statistic

Let `ι` be a finite index set, `V` a real `ι × ι` matrix, `T` a linear subspace of the Euclidean
space `ℝ^ι` and `z ∈ ℝ^ι`. With `W` the [whitening matrix](whitening.md) of `V`, the Gaussian
projection statistic is `S(V, T, z) = ‖P (W z)‖ ^ 2`, where `P` is the orthogonal projection onto
the orthogonal complement of `W T = {W u : u ∈ T}`: the squared length of the component of `W z`
orthogonal to `W T`. For positive definite `V` it is the
[minimum of the residual quadratic form](gauss-proj-stat-eq-i-inf.md) `(z - u)ᵀ V⁻¹ (z - u)` over
`u ∈ T`. The definition is total in `V`: when `V` is not positive definite, `W = 0`, so `W T = {0}`,
`P` is the identity and `S(V, T, z) = 0` for all `T` and `z`. The intended domain is positive
definite `V`, the covariance matrix of a centred Gaussian vector `z`.
