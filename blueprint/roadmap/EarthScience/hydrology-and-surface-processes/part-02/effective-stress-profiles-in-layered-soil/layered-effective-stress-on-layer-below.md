# Effective stress in a layer below the water table

Let `t i ≥ 0` be the thicknesses of the layers `i = 0, 1, …` (for every `i`), so that layer `i`
lies between the depths `z_i = ∑_{j<i} t j` and `z_{i+1}`, and let `γ i` be the layer unit
weights and `q` a surcharge (real numbers). Let the water table lie at the top of layer `m`,
at depth `z_m`, and let `γw` be the unit weight of water. If `k < n`, `m ≤ k` and
`z_k ≤ z ≤ z_{k+1}`, the effective stress of the `n` layers at depth `z` is
`σ'(z) = q + ∑_{i<k} γ i * t i + γ k * (z - z_k) - γw * (z - z_m)`.
