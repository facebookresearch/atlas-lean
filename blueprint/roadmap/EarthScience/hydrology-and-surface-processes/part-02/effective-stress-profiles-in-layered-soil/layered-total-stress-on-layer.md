# Total vertical stress within a layer

Let `t i ≥ 0` be the thicknesses of the layers `i = 0, 1, …` (for every `i`), so that layer `i`
lies between the depths `z_i = ∑_{j<i} t j` and `z_{i+1}`, and let `γ i` be the layer unit
weights and `q` a surcharge (real numbers). If `k < n` and `z_k ≤ z ≤ z_{k+1}`, the
total vertical stress of the `n` layers at depth `z` is the surcharge plus the completed layers
plus `γ k` times the depth into layer `k`:
`σ(z) = q + ∑_{i<k} γ i * t i + γ k * (z - z_k)`.
