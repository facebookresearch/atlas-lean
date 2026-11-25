# Particular steady-state response of the forced mass–spring–damper

For real numbers `m`, `c`, `k`, `F`, `Ω` and a time `t`, the particular (steady-state) response is

`x_p(t) = A cos (Ω t) + B sin (Ω t)`,

with the [in-phase coefficient](steady-state-cos.md) `A = F (k - m Ω²) / D` and the
[quadrature coefficient](steady-state-sin.md) `B = F c Ω / D`, where `D = (k - m Ω²)² + (c Ω)²`.
When `D ≠ 0` it solves `m x'' + c x' + k x = F cos (Ω t)`
([equation](particular-response-solves.md)); with the convention `u / 0 = 0` it is identically `0`
when `D = 0`.
