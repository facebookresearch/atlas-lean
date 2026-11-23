# Shallow water riemann invariant transport

Riemann-invariant transport for 1D flat-bed shallow water at a wet
point. Let `h` be the depth and `u` the velocity, with time and space
slices differentiable at `(t, x)` with partials `hₜ`, `hₓ`, `uₜ`, `uₓ`,
let gravity and the depth there be positive, and let the primitive
equations `hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0` hold at
`(t, x)`. Then, with `c = √(g h)`, both paired transport equations
`(∂ₜ + (u + c) ∂ₓ)(u + 2 c) = 0` and `(∂ₜ + (u - c) ∂ₓ)(u - 2 c) = 0`
hold at `(t, x)`.
