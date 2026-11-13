# The singular Gaussian on the hyperplane `(√p)ᗮ`

For a probability vector `p`, the
projection `P_K Z` of a standard Gaussian `Z` on `EuclideanSpace ℝ ι` onto `K = (√p)ᗮ` has every
coordinate projection `⟪P_K Z, t⟫` centered normal with variance `‖t‖² - ⟪√p, t⟫²`: its
covariance is `I - √p √pᵀ`, singular in the direction `t = √p`. This geometric statement holds
for any nonnegative `p` summing to `1`.

When all `pᵢ > 0`, `P_K Z` is the limit in `tendstoInDistribution_pearsonResidual`, and
`I - √p √pᵀ` is the multinomial covariance `diag p - p pᵀ` in the weighted coordinates
`xᵢ / √pᵢ`. With a zero cell neither identification holds: the residual in a cell with
`pᵢ = 0` is identically `0` (Lean's `x / 0 = 0`), while for `p = (1, 0)` and `t` the second
coordinate vector the variance above is `1`.
