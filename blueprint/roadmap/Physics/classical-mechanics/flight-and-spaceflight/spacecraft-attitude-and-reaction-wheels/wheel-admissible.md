# Admissible reaction-wheel command on a finite horizon

For real numbers `umax`, `hmax` and `T` and real functions `u` and `h` of time, the command `u`
with wheel momentum `h` is admissible on the horizon `[0, T]` for the command limit `umax` and
the momentum limit `hmax` when `T ≥ 0` and, at every `t ∈ [0, T]`,

`|u(t)| ≤ umax` and `|h(t)| ≤ hmax`.

The definition does not relate `u` and `h`. In the reduced fixed-axis wheel model, `h` is the
wheel's angular momentum relative to the body, so `hmax` is a wheel-speed limit, and `u = h'` is
its commanded rate. In the physical reading both limits are nonnegative; since `0 ∈ [0, T]`, no
command is admissible when `umax < 0` or `hmax < 0`.
