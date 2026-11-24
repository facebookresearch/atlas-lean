# Explicit Euler step for a body in a bath

For real numbers `C`, `G`, `T_amb`, `dt` (time step) and `T`, the explicit Euler step of
`C T' = Q(T)` maps `T` to `T + dt Q(T) / C`, with the [bath power](bath-power.md) `Q`. With the
convention `a / 0 = 0`, it leaves `T` unchanged when `C = 0`.
