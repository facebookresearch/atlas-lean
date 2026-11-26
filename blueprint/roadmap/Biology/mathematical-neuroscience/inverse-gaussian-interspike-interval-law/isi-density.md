# Inverse Gaussian first-passage density

The function
`z₀ (4π)^{-1/2} T^{-3/2} exp(-(z₀ - cT)² / (4T))` of all real `z₀`, `c` and `T`. For `z₀ > 0` it
is, on times `T > 0`, the density of the finite values of the first passage time of
`c t + √2 B(t)` to `z₀` (`measure_firstPassageTime_mem_Icc`). Its total mass on `T > 0` is `1`
when `c ≥ 0`; with negative drift `c < 0` it is a subprobability density of total mass
`exp(c z₀) < 1`, the remaining mass being at `⊤` (paths that never reach the threshold). Outside
this domain the formula is not a density: at `z₀ = -1`, `c = 0`, `T = 1` it is negative.
