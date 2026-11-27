# Sabine reverberation time T60 of a room

For real `V`, `c` and `A`, the Sabine reverberation time is `T60 = 24 ln 10 · V / (c A)`, with `ln`
the natural logarithm (`24 ln 10 ≈ 55.26`). In the Sabine model of a room, `V` is the volume, `c`
the speed of sound and `A` the equivalent absorption area, all positive; then `T60` is the time at
which the [Sabine energy](sabine-energy.md) decaying at the [Sabine rate](sabine-rate.md)
`k = c A / (4 V)` from a positive initial energy `E₀` has fallen by a factor `10⁶`, that is by
`60 dB` on the energy scale `10 log₁₀` ([energy at T60](sabine-energy-at-t60.md)). The definition
takes any real values, and with the convention `x / 0 = 0` it is `0` when `c A = 0`, for example for
zero absorption.
