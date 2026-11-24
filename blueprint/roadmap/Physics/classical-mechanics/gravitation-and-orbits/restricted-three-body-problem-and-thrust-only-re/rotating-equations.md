# Off the primaries, Newton's law gives the rotating equations

Let `μ` and `t` be real, and let the rotating-frame coordinates `x, y : ℝ → ℝ` of a particle moving
in the orbital plane be twice continuously differentiable on `ℝ`. Suppose that at the time `t` the
particle is off both primaries, `r₁ > 0` and `r₂ > 0` at `(x(t), y(t))`, and that its inertial
position `X(s) = R(s) (x(s), y(s), 0)`, with `R(s)` the
[orientation of the rotating frame](rotating-frame.md), obeys Newton's law `X''(t) = g(X(t), t)`
under the [field of the two primaries](primary-gravity.md) `g`. Then, at the time `t`,

`x'' - 2 y' = Ω_x` and `y'' + 2 x' = Ω_y`,

where `Ω_x` and `Ω_y` are the partial derivatives of the
[effective potential](effective-potential.md) at `(x(t), y(t))`:
`Ω_x = x - (1 - μ) (x + μ) / r₁³ - μ (x - (1 - μ)) / r₂³` and
`Ω_y = y - (1 - μ) y / r₁³ - μ y / r₂³`
(see the [first](has-deriv-at-effective-potential-fst.md) and
[second](has-deriv-at-effective-potential-snd.md) partial derivatives). The terms `-2 y'` and
`2 x'` come from the [Coriolis acceleration](coriolis-power-eq-zero.md) of the counterclockwise
unit-rate rotation. Newton's law is assumed only at the time `t`, and the equations are concluded
at `t`. In the physical reading `0 < μ < 1`; the result holds for every real `μ`.
