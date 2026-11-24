# Algebraic decomposition of the acceleration in a rotating frame

For all vectors `Ω`, `v`, `a` and `r` of `ℝ³`,

`(a + Ω × v) + Ω × (v + Ω × r) = a + 2 (Ω × v) + Ω × (Ω × r)`,

where `×` is the cross product of `ℝ³`, `x × y = (x₁ y₂ - x₂ y₁, x₂ y₀ - x₀ y₂, x₀ y₁ - x₁ y₀)` for
components indexed `0, 1, 2`.

In a frame rotating with constant angular velocity `Ω` about a fixed origin shared with the inertial
frame, with position `r`, velocity `v` and acceleration `a` measured in the rotating frame, the left
side is the inertial acceleration written as the rotating-frame derivative `a + Ω × v` of the
inertial velocity `v + Ω × r` plus the transport term `Ω × (v + Ω × r)`. On the right, `2 (Ω × v)`
is the Coriolis term and `Ω × (Ω × r)` the centripetal term, which points toward the rotation axis;
its negative is the centrifugal acceleration of the rotating-frame equation of motion. The Euler
term `Ω̇ × r` does not appear because `Ω` is constant. The identity itself is pure algebra and holds
for all vectors.
