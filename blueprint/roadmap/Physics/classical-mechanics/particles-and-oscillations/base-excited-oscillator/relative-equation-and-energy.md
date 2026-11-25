# Relative equation and relative-energy identity at one time

Let `m`, `c` and `k` be real numbers and `x`, `y`, `u`, `x_v`, `y_v`, `x_a`, `y_a` and `p` real
functions of time with `u(s) = x(s) - y(s)` at every time `s`. Fix a time `t` at which `x` has
derivative `x_v(t)`, `y` has derivative `y_v(t)`, `x_v` has derivative `x_a(t)`, `y_v` has
derivative `y_a(t)`, and the base-excited equation

`m x_a(t) + c (x_v(t) - y_v(t)) + k (x(t) - y(t)) = p(t)`

holds. Then, at `t`:

1. `u` has derivative `x_v(t) - y_v(t)`, and `s ↦ x_v(s) - y_v(s)` has derivative
   `x_a(t) - y_a(t)`;
2. the relative equation holds:
   `m (x_a(t) - y_a(t)) + c (x_v(t) - y_v(t)) + k u(t) = p(t) - m y_a(t)`;
3. the function `s ↦ (m / 2) (x_v(s) - y_v(s))² + (k / 2) u(s)²` has derivative
   `(x_v(t) - y_v(t)) (p(t) - m y_a(t)) - c (x_v(t) - y_v(t))²`.

When `x_v` and `y_v` are the velocities of `x` and `y` on a neighbourhood of `t`, `x_a(t) - y_a(t)`
is `u''(t)` and the function in (3) is the relative energy, whose rate is the power of the
effective force `p - m y_a` minus the viscous dissipation. In the physical reading `m > 0`, `c ≥ 0`
and `k > 0`; the identities hold for all real `m`, `c` and `k`.
