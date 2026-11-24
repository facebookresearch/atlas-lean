# Rotating acceleration decomposition

Constant-rate rotating-frame acceleration decomposition (algebraic form,
declared sign convention: inertial acceleration = rotating-frame derivative
of the inertial velocity plus the transport correction `Ω × w`):
`(a + Ω × v) + Ω × (v + Ω × r) = a + 2 • (Ω × v) + Ω × (Ω × r)`,
where `a` is the rotating-frame acceleration, `v` the rotating-frame
velocity, `r` the position, and `Ω × ·` is the Mathlib cross product `⨯₃`.
The first term on the right is the rotating-frame acceleration, the
second is Coriolis, the third centripetal (its negative is the
centrifugal acceleration). The Euler term `Ω̇ × r` vanishes for constant
`Ω` and does not appear.
