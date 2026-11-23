# Depth of the top of a layer

For layer thicknesses `t 0, t 1, …` (real numbers) and an index `k`, the depth of the top of layer
`k` is the prefix sum of the thicknesses above it: `z_k = ∑_{i<k} t i`. In particular `z_0 = 0`,
the ground surface.
