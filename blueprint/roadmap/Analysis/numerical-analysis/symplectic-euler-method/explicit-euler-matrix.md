# Step matrix of the explicit Euler method for an oscillator

For real numbers `m`, `k` and `h`, the explicit Euler step matrix acting on the state `(q, p)` is
the 2 × 2 matrix with rows `(1, h / m)` and `(-h k, 1)`: the update `q' = q + h p / m`,
`p' = p - h k q` for the harmonic oscillator. With the convention `a / 0 = 0`, the entry `h / m` is
`0` when `m = 0`; the intended domain is `m > 0`.
