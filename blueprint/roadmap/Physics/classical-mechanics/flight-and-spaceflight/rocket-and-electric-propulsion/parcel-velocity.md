# Velocity after one parcel step

For reals `m`, `v`, `q`, `ve`, `F` and `h`, `v_h = (m v + F h − q h (v − ve)) / (m − q h)`: the
vehicle velocity after a step of length `h` from the state `(m, v)` in which a parcel of mass `q h`
leaves with velocity `v − ve` and the external force `F` acts, obtained by solving the momentum
balance `(m − q h) v_h + q h (v − ve) = m v + F h`. With the convention `x / 0 = 0`, `v_h = 0` when
the remaining mass `m − q h` is `0`, where the balance has no solution in general. In the physical
reading `m − q h > 0`, `q ≥ 0` and `h > 0`.
