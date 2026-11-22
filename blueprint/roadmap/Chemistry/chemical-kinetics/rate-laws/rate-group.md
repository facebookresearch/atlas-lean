# Rate Group

The scalar `k * t * [A]₀ ^ (n - 1)` through which the integrated laws of order `n` depend on
`k`, `t` and `[A]₀` (`zeroOrderSol_rateGroup`, `firstOrderSol_rateGroup`,
`secondOrderAASol_rateGroup`). This is a normalization identity in real arithmetic: no dimensions
or units are formalized here. At order `0` it divides by `[A]₀`, so it is meaningful for
`[A]₀ > 0` (as `k_of_rateGroup` assumes).
