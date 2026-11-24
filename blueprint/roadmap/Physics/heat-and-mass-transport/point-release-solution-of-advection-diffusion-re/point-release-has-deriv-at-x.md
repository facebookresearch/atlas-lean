# The point-release kernel is differentiable in x for all parameters

For all real `M`, `D`, `k`, `U`, `t` and `x`, the
[point-release kernel](point-release-solves-adr.md)
`c(t, x) = M e^{-kt} exp(-(x - Ut)²/(4Dt)) / √(4πDt)`, as a function of position, is differentiable
at `x`. When `Dt ≤ 0` the kernel is the constant `0` in `x`, by `√y = 0` for `y < 0` and `y/0 = 0`.
