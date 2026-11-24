# Symplectic Euler Matrix

The momentum-first (symplectic Euler) step matrix for the harmonic
oscillator with mass `m`, stiffness `k`, and step `h`, acting on the
state `(q, p)`: `p' = p - h * k * q`, `q' = q + h * p' / m`, so
`M = [[1 - h^2 * k / m, h / m], [-h * k, 1]]` in `(q, p)` coordinates,
written with `Matrix.of` over `Fin 2`.
