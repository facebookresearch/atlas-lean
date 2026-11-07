# Norm of a cusp form

The product norm of a cusp form: for `𝒢` of finite relative index in `ℋ`,
the product of the `ℋ / 𝒢`-translates of `f`, viewed as a cusp form on the
larger group `ℋ` at weight `k * [ℋ : 𝒢]`. This lifts Mathlib's
`ModularForm.norm` to cusp forms; the only new work is checking vanishing
at the cusps, which follows because each translate is a cusp form.
