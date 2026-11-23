# Scale function normalized at an arbitrary base point

For real functions `b`, `a` and real numbers `c`, `p`, let

`S_c(p) = ∫_c^p ψ(y) dy`,

where `ψ` is the [scale density](../selection-duality-and-general-one-dimensional-di/scale-density.md) of drift `b` and variance `a`. The integral is oriented
(`∫_c^p = -∫_p^c` when `p < c`) and is taken to be `0` when `ψ` is not integrable between `c` and
`p`. Unlike the [scale function](../selection-duality-and-general-one-dimensional-di/scale-function.md) `S`, which is normalized by `S(0) = 0`, the base point `c` is arbitrary:
`S_c(c) = 0`. For a [regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md) and `c, p ∈ [0, 1]`,
[the two differ by a constant](scale-function-from-eq-sub.md): `S_c(p) = S(p) - S(c)`.
