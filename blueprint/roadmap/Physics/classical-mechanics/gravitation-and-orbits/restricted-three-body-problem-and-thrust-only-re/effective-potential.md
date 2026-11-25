# Effective potential of the restricted three-body problem

For reals `μ`, `x` and `y`, the effective potential of the rotating frame at the point `(x, y)`
of the orbital plane is

`Ω(x, y) = (x² + y²) / 2 + (1 - μ) / r₁ + μ / r₂`,

with `r₁` and `r₂` the distances to the [first](primary-dist-one.md) and
[second](primary-dist-two.md) primaries, of masses `1 - μ` at `(-μ, 0)` and `μ` at `(1 - μ, 0)`.
It enters the [rotating equations](rotating-equations.md) with a plus sign,
`x'' - 2 y' = Ω_x` and `y'' + 2 x' = Ω_y`. The intended domain is off both primaries. With the
convention `u / 0 = 0` the formula takes the finite value `μ² / 2 + μ` at the first primary and
`(1 - μ)² / 2 + (1 - μ)` at the second, where the physical potential of a positive mass is
singular. In the physical reading `0 < μ < 1`; the definition takes any real `μ`.
