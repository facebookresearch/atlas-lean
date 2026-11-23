# Inverse prediction as a function of three inputs

Inverse prediction as a function of its three inputs `v = (y₀, a, b)`, indexed `0`, `1`, `2` in
the order of the [gradient of inverse prediction](inverse-prediction-gradient.md):
`f(v) = (v 0 - v 1) / v 2`, that is `f(y₀, a, b) = (y₀ - a) / b`. This is the measurement
function to which the first-order law of propagation applies. For `b = 0` the convention
`x / 0 = 0` makes it `0`; the intended domain is `b ≠ 0`.
