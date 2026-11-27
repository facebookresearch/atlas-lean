# Cosine coefficients of a unit point charge

For real numbers `L` and `x₀` and a natural number `n`, the point-charge coefficients are

`g_0 = 1 / L` and `g_n = (2 / L) cos (n π x₀ / L)` for `n ≥ 1`,

the `0`-th one being `(1 / L) cos 0`. For `L > 0` and `x₀ ∈ [0, L]` they are the cosine
coefficients of a unit point charge at `x₀` on the sealed cable `[0, L]`: the values
`cos (n π x₀ / L)` of the [modes](cos-mode.md) at `x₀`, divided by the self-inner-products `L` and
`L / 2`. The formula is defined for every real `L` and `x₀`: with the convention `u / 0 = 0`, every
coefficient is `0` when `L = 0`, and for every `L` it is even and `2L`-periodic in `x₀`
([even](green-coeff-neg-source.md), [periodic](green-coeff-add-two-mul-source.md)), so a source
outside `[0, L]` has the coefficients of its image inside. The coefficients are bounded by `2 / |L|`
([bound](abs-green-coeff-le.md)).
