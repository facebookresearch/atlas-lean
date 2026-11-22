# Capital Elasticity

Output elasticity of the production function `F` with respect to capital:
`K * F_K / F`, where `F_K = fderiv ℝ F (K, L) (1, 0)` is the partial derivative
of `F` in its first argument (source clause: "capital elasticity"). As a total
function: if `F` is not differentiable at `(K, L)` or `F (K, L) = 0`, the total
`fderiv` and division may yield junk values.
