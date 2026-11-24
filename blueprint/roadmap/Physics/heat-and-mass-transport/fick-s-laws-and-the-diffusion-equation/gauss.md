# Gaussian concentration with total mass M on the line

For real `M`, `D`, `x` and `t`, the Gaussian is

`G(x, t) = M/√(4πDt) · exp(-x²/(4Dt))`.

It depends on `D` and `t` only through `Dt`. It is meant for `D > 0` and `t > 0`; when `Dt ≤ 0`, for
example for `D > 0` and `t ≤ 0`, the square root is `0` and, with `M/0 = 0`, the value is `0`. With
no drift and no reaction, the
[point-release kernel](../point-release-solution-of-advection-diffusion-re/point-release-solves-adr.md)
reduces to this formula. In the physical reading `M` is the released mass and `D > 0` the
diffusivity.
