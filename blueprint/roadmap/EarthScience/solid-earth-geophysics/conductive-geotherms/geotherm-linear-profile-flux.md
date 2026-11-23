# Geotherm linear profile flux

The linear profile `T(z) = T₀ - (2 / 100) * z` has derivative
`-(2 / 100)` everywhere, so with `k = 3` its conductive flux is
`-k * T' = 6 / 100`. The derivative is `EarthScience.hasDerivAt_slab_profile`
with `L = 100` and `TL = T₀ - 2`.
