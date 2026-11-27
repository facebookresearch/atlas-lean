# Coriolis and centripetal terms from the frame transport law

Let `Ω` be a constant vector of `ℝ³`, `r, v : ℝ → ℝ³`, `a` and `a_I` vectors of `ℝ³` and `t` real.
Suppose that `r` has derivative `v(t)` at `t`, that `v` has derivative `a` at `t`, and that `a_I`
obeys the frame transport law for `w(s) = v(s) + Ω × r(s)`: `a_I = w'(t) + Ω × w(t)`, where `w'(t)`
is the derivative of `w` at `t`. Then

- `w` has derivative `a + Ω × v(t)` at `t`, and
- `a_I = a + 2 (Ω × v(t)) + Ω × (Ω × r(t))`.

Here `×` is the cross product of `ℝ³`, `x × y = (x₁ y₂ - x₂ y₁, x₂ y₀ - x₀ y₂, x₀ y₁ - x₁ y₀)` for
components indexed `0, 1, 2`. In the rotating-frame reading, `r`, `v` and `a` are the position,
velocity and acceleration measured in a frame rotating with constant angular velocity `Ω` about a
fixed origin shared with the inertial frame, `w` is the inertial velocity expressed in that frame,
and `a_I` the inertial acceleration, expressed in that frame: it is the
rotating-frame acceleration plus the Coriolis term `2 (Ω × v)` and the centripetal term
`Ω × (Ω × r)` ([algebraic decomposition](rotating-acceleration-decomposition.md)). The transport law
is assumed, not derived.
