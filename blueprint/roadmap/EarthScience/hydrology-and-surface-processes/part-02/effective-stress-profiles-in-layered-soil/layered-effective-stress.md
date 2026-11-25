# Effective vertical stress in a layered soil

For `n` layers with thicknesses `t i` and unit weights `γ i`, a surcharge `q`, a unit weight of
water `γw`, a water-table depth `zw` and a depth `z` (real numbers), the effective vertical stress
is the [total stress](layered-total-stress.md) minus the
[static pore pressure](static-pore-pressure.md):
`σ'(z) = q + ∑_{i<n} γ i * d_i(z) - γw * max (z - zw) 0`, where `d_i(z)` is the
[thickness of layer `i` traversed](traversed-thickness.md) down to `z`.
