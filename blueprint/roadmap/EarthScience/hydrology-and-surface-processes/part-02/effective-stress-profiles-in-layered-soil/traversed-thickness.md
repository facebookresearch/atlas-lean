# Thickness of a layer traversed down to a depth

For layer thicknesses `t 0, t 1, …`, with `z_i = ∑_{j<i} t j` the depth of the top of layer `i`,
the thickness of layer `i` traversed down to the depth `z` is
`d_i(z) = max z_i (min z z_{i+1}) - z_i`, the depth clamped to the layer interval. For `t i ≥ 0`
it is `0` for `z ≤ z_i`, `z - z_i` for `z_i ≤ z ≤ z_{i+1}` and `t i` for `z ≥ z_{i+1}`; for a
negative thickness `t i < 0` it is `0` at every depth.
