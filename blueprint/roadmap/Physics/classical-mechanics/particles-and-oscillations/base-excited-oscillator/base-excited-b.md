# Input matrix of the base-excited oscillator

For a real number `m`, the input matrix of the base-excited oscillator is the `2 × 2` real matrix

`B = [[0, 0], [1 / m, -1]]`,

acting on the input `(p, a_g)`, the applied force and the base acceleration: the force enters the
velocity row with gain `1 / m`, the base acceleration with gain `-1`, and neither enters the
displacement row. The force channel is that of the
[phase-space forcing](../forced-damped-oscillator-and-resonance/phase-forcing.md) `(0, F cos (Ω t) / m)` of the mass–spring–damper. In
the physical reading `m > 0`; with the convention `u / 0 = 0` the force gain is `0` when `m = 0`.
