# Output elasticity with respect to capital

The output elasticity of a production function `F : ℝ × ℝ → ℝ` with respect to
capital at `(K, L)` is `ε_K = K * F_K / F(K, L)`, where `F_K` is the derivative
of `F` at `(K, L)` applied to the direction `(1, 0)`, the partial derivative in
the first argument. The definition is total: the derivative of a function that
is not differentiable at `(K, L)` is taken to be `0`, and `x / 0 = 0`, so
`ε_K = 0` when `F` is not differentiable at `(K, L)` or `F(K, L) = 0`.
