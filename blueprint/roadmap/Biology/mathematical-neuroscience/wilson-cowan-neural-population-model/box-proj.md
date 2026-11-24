# Coordinatewise projection onto a square box

For `U ≥ 0` and a state `x = (x₀, x₁)` in `ℝ²`, the box projection is the point of the box
`[0, U] × [0, U]` whose coordinates are `max(0, min(U, xᵢ))`: each coordinate is clamped to `[0, U]`
([coordinate formula](box-proj-apply.md)). The hypothesis `U ≥ 0` makes the box nonempty.
