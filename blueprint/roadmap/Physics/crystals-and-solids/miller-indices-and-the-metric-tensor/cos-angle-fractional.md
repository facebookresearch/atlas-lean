# Angles from the metric tensor

The angle `θ` between the vectors with fractional
coordinates `v` and `w` (Mathlib's `InnerProductGeometry.angle`) satisfies
`cos θ = (∑ i j, v i * G i j * w j) / (√(∑ i j, v i * G i j * v j) * √(∑ i j, w i * G i j * w j))`.
If one of the vectors is zero, Mathlib's angle is `π / 2` and both sides are `0`.
