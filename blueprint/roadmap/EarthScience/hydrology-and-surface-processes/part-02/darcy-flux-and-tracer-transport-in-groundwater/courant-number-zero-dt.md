# A zero time step gives Courant number zero

For all real `q`, `n` and `dx`, the Courant number with time step `0` is `|q / n| * 0 / dx = 0`.
At `dx = 0` the quotient is `0 / 0`, which is `0` by the convention `x / 0 = 0`; the intended
domain is `dx > 0`.
