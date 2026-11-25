# Vapour pressure at an interface of layers in series

For a natural number `n`, layer vapour resistances `R : ℕ → ℝ`, boundary partial pressures `p_in`,
`p_out` and an index `m`, the vapour pressure after the first `m` layers is

`p_m = p_in - g ∑_{i < m} R_i`,

with `g` the [steady series flux](vapor-series-flux.md). The modelled interfaces are `m ≤ n`; for
`m > n` the formula continues the partial sums formally and is not an interface.
