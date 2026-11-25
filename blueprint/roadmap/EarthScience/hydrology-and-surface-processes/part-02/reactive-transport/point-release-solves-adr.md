# For D, t > 0 the point release solves advection–diffusion–reaction

Let `D > 0` and `t > 0`, and let `M`, `k`, `U` and `x` be real. The point-release kernel

`c(t, x) = M e^{-kt} exp(-(x - Ut)²/(4Dt)) / √(4πDt)`

satisfies at `(t, x)`

`c_t + U c_x = D c_xx - k c`,

with derivatives in one variable holding the other fixed. They exist: the kernel is
[differentiable in time](point-release-has-deriv-at-t.md),
[in position](point-release-has-deriv-at-x.md), and
[twice in position](point-release-has-deriv-at-xx.md). The identity holds for every real `k`; the
reaction is a decay only for `k ≥ 0`. In the physical reading `M` is the released mass, `U` the
drift velocity and `D` the diffusivity.
