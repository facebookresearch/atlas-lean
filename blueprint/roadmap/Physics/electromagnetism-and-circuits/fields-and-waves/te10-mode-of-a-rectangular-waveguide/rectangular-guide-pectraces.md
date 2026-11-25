# PEC trace conditions on the four side walls of a rectangular guide

For reals `a`, `b` and fields `E, B : ℝ³ → ℝ³` (components indexed `0, 1, 2` for `x, y, z`), the PEC
trace conditions hold if `a > 0`, `b > 0`, and the tangential electric field and the normal magnetic
field vanish on the four side walls: at the points `(0, y, z)` and `(a, y, z)` with `0 ≤ y ≤ b` and
any `z`, the [tangential electric field](tangential-electric-on-xwall.md) and the
[normal magnetic field](normal-magnetic-on-xwall.md) of an `x`-wall vanish, and at the points
`(x, 0, z)` and `(x, b, z)` with `0 ≤ x ≤ a` and any `z`, the
[tangential electric field](tangential-electric-on-ywall.md) and the
[normal magnetic field](normal-magnetic-on-ywall.md) of a `y`-wall vanish.

Written face by face as component equations, the conditions are `a > 0`, `b > 0`,
`E_y = E_z = B_x = 0` on the walls `x = 0` and `x = a`, and `E_x = E_z = B_y = 0` on the walls
`y = 0` and `y = b`, over the same ranges ([equivalence](traces-iff-component-conditions.md)). The
corner lines belong to both adjacent walls. For a nonpositive width the conditions fail for every
field.
