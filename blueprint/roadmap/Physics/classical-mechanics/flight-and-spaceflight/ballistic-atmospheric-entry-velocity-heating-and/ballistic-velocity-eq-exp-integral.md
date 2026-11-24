# Ballistic Velocity eq exp integral

Integrated form of `dv/dh = ρ(h) * v / (2 * β * sin γ)`: the exponent of the profile is the
column mass between `he` and `h` divided by `2 * β * sin γ`. The identity of the two formulas
holds for `H ≠ 0`, all other parameters arbitrary; it is the integrated drag equation only for
`β > 0` and `sin γ > 0`, where `2 * β * sin γ ≠ 0` (`hasDerivAt_ballisticVelocity`).
