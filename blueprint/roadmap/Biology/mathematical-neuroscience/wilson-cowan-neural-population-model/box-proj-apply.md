# Each projected coordinate is clamped to the interval from 0 to U

For `U ≥ 0`, every state `x` in `ℝ²` and each coordinate `i`, the `i`-th coordinate of the
[box projection](box-proj.md) of `x` is `max(0, min(U, xᵢ))`.
