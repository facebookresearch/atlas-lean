# Derivative of the fixed-axis orientation

For every rigid body in three dimensions, all real numbers `ω₀` and `α` and every time `t`, the
orientation `R(t) = Rz(θ(t))` of the [fixed-axis motion](fixed-axis-motion.md) has derivative
`Ṙ(t) = θ'(t) D(θ(t))`, where `θ` is the [rotation angle](fixed-axis-angle.md) and `D(θ)` is the
matrix with rows `(-sin θ, -cos θ, 0)`, `(cos θ, -sin θ, 0)` and `(0, 0, 0)`, the derivative of
[`Rz`](../body-fixed-and-inertial-frames/rot-z.md) at `θ`.
