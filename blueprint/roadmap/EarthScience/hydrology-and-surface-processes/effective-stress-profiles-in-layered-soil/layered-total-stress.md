# Total vertical stress in a layered soil

For `n` layers with thicknesses `t i` and unit weights `γ i`, a surcharge `q` and a depth `z`
measured downward from the ground surface (real numbers), the total vertical stress is the
surcharge plus the weight of the traversed layers: `σ(z) = q + ∑_{i<n} γ i * d_i(z)`, where
`d_i(z)` is the [thickness of layer `i` traversed](traversed-thickness.md) down to `z`.
