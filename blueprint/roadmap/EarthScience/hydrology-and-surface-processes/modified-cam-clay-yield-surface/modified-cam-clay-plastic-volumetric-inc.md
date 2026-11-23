# Associated-flow plastic volumetric increment

For real `M`, `pc`, `p` and a plastic multiplier `λ`, the plastic volumetric increment of
associated flow is the multiplier times the partial derivative of the yield function in `p`:
`Δε = λ * M ^ 2 * (2 * p - pc)`. It uses the compression-positive strain convention: a
positive increment is compactive, a negative one dilative. It is a quantity at a fixed stress
point, not an evolution law.
