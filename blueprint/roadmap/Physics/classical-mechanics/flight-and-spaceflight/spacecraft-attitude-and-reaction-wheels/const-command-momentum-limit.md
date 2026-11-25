# A nonzero constant wheel command saturates the momentum in finite time

Let `c ≠ 0`, `umax` and `hmax` be real numbers and `h` a real function of time with the
derivative `c` at every `t ≥ 0` and `|h(0)| ≤ hmax`. Then there is a time `T_sat ≥ 0` with
`|h(T_sat)| = hmax`, and for every `T > T_sat` the constant command `u(t) = c` with momentum `h`
is not [admissible](wheel-admissible.md) on `[0, T]` for the limits `umax` and `hmax`, whatever
the command limit `umax`. Since `h(t) = h(0) + c t` for `t ≥ 0`, one can take
`T_sat = (hmax − h(0)) / c` for `c > 0` and `T_sat = (−hmax − h(0)) / c` for `c < 0`.
