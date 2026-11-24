# Step matrix of the symplectic Euler method for an oscillator

For real numbers `m` (mass), `k` (stiffness) and `h` (step), the symplectic Euler step matrix acting
on the state `(q, p)` is the 2 × 2 matrix with rows `(1 - h² k / m, h / m)` and `(-h k, 1)`: the
momentum-first update `p' = p - h k q`, `q' = q + h p' / m` for the harmonic oscillator. With the
convention `a / 0 = 0`, the entries with `m` in the denominator are `0` when `m = 0`; the intended
domain is `m > 0`.
