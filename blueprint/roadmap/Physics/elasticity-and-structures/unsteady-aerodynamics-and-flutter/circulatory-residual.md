# Residual of the circulatory two-mode model

For a real `q` and a trajectory `z : ℝ → ℝ²` in nondimensional time, the residual at time `t` is
`z''(t) + 2 z'(t) + z(t) - q J z(t)`, with `J` the [circulatory load operator](circulatory-j.md):
two modes with unit masses, unit stiffnesses and damping `2`, under the circulatory load `q J z`. A
solution makes the residual vanish at every `t`. Derivatives are taken to be `0` where `z` or `z'`
is not differentiable.
