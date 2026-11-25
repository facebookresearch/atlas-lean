# Effective stress within a layer for any water-table depth

Let `t i ≥ 0` be the thicknesses of the layers `i = 0, 1, …` (for every `i`), so that layer `i`
lies between the depths `z_i = ∑_{j<i} t j` and `z_{i+1}`, and let `γ i` be the layer unit
weights and `q` a surcharge (real numbers). Let `γw` be the unit weight of water and `zw` any
water-table depth. If `k < n` and `z_k ≤ z ≤ z_{k+1}`, the effective stress of the `n` layers at
depth `z` is the affine total stress minus the static pore pressure:
`σ'(z) = q + ∑_{i<k} γ i * t i + γ k * (z - z_k) - γw * max (z - zw) 0`, which is affine on
each side of the table.
