# For D, t > 0 the point-release inventory is M e^−kt

Let `D > 0` and `t > 0`, and let `M`, `k` and `U` be real. The
[point-release kernel](point-release-solves-adr.md)
`c(t, x) = M e^{-kt} exp(-(x - Ut)²/(4Dt)) / √(4πDt)` has the total inventory

`∫_ℝ c(t, x) dx = M e^{-kt}`.

For `M > 0` it decays when `k > 0`, is constant in time when `k = 0`, and grows when `k < 0`.
