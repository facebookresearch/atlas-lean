# Gravitational field of the two primaries in the inertial frame

For reals `μ` and `t` and an inertial position `X` (a real triple), the field of the two primaries
is

`g(X, t) = -(1 - μ) (X - P₁(t)) / |X - P₁(t)|³ - μ (X - P₂(t)) / |X - P₂(t)|³`,

the sum of the [point-mass pulls](point-mass-pull.md) of the first primary, of mass `1 - μ` at
`P₁(t) = R(t) (-μ, 0, 0)`, and of the second, of mass `μ` at `P₂(t) = R(t) (1 - μ, 0, 0)`, with
gravitational constant one, the Euclidean length `|·|` and `R(t)` the
[orientation of the rotating frame](rotating-frame.md). The primaries are fixed in the rotating
frame, a unit distance apart, and their barycenter is the origin. The intended domain is off both
primaries: at `X = P₁(t)` the first term is the zero vector, so the value is the second primary's
pull alone, and at `X = P₂(t)` it is the first primary's pull alone. In the physical reading
`0 < μ < 1`, so both masses are positive (with the usual convention `0 < μ ≤ 1/2` the first
primary is the larger); the definition takes any real `μ`.
