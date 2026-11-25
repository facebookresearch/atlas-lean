# Time shift of a signal

Time shift of a raw pointwise signal, as a linear map: `shiftₗ 𝕜 E a`
sends `x` to the signal `t ↦ x (t - a)` (delay by `a` when `a` is positive). It is `LinearMap.funLeft` along `t ↦ t - a`.
