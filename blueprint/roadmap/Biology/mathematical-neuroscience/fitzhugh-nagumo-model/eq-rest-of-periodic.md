# Periodic orbits must enter the band `restFactor > 0`

For `b, ε > 0` and an equilibrium
`(vr, wr)`, a `T`-periodic solution (`T > 0`) along which `restFactor vr (v - vr) ≤ 0` at all
times is the constant rest state.

Proof: `restEnergy` is antitone (its derivative is `restFlux ≤ -2 b (w - wr)² ≤ 0`) and
`T`-periodic, hence constant on `[0, ∞)`; so `restFlux = 0` on `(0, ∞)`, forcing `w = wr` there,
and then `w' = ε (v - vr) = 0` forces `v = vr`. The time `0` follows by periodicity.
