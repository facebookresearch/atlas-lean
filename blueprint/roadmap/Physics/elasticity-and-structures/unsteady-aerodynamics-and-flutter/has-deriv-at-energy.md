# Energy balance of the circulatory model

For every real `q` and every twice continuously differentiable trajectory `z : ℝ → ℝ²`, the energy
`E(s) = (z'(s) · z'(s) + z(s) · z(s)) / 2` has, at every time `t`, the derivative
`r(t) · z'(t) - 2 z'(t) · z'(t) + (q J z(t)) · z'(t)`, where `r` is the
[residual](circulatory-residual.md). On a solution (`r = 0`) the
damping removes `2 z' · z'` and the [circulatory force](circulatory-force.md) supplies the power
`(q J z) · z'`.
