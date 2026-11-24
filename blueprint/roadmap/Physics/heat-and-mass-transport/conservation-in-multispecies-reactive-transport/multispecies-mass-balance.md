# Multispecies mass balance

Multispecies mass balance on a one-dimensional box `[a, b]`, at time
`t`. Under the hypotheses of `multispecies_integrated`, the conserved
inventory `t ↦ ∫ x in a..b, l ⬝ᵥ c t x` has derivative
`-(l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a))` at `t`: it changes only by the net boundary
flux. Two further hypotheses are explicit: `hswap`, differentiation under the
integral sign per species (each `t ↦ ∫ x in a..b, c t x i` has derivative
`∫ x in a..b, ∂ₜ c t x i` at `t`), and `hc_all`, interval integrability of
every species concentration on `[a, b]` at every time `t'`, which is used to
split the inventory into per-species integrals. Without `a ≤ b` this is a
signed identity for the oriented integral; the inventory interpretation
requires `a ≤ b`.
