# Base-excited oscillator

Relative-coordinate oscillator identities at one time `t`.
The absolute coordinate `x` obeys the base-excited equation
`m * xa + c * (xv - yv) + k * (x - y) = pf` at `t`, where `y` is the
base displacement with acceleration value `ya t`. For the relative
displacement `u = x - y` (all times, so `u` is identified near `t`):
(1) `u` has velocity `xv t - yv t` at `t`, and the supplied relative
    velocity function `s ↦ xv s - yv s` has derivative
    `xa t - ya t` at `t`;
(2) the relative equation `m * (xa t - ya t) + c * (xv t - yv t)
    + k * u t = pf t - m * ya t` holds at `t`;
(3) the energy expression `m/2 * (xv-yv)^2 + k/2 * u^2` has
    derivative `(xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t)^2`
    at `t`.
Here `xa t - ya t` is `u''(t)`, and the energy expression is the
relative energy, when `xv` and `yv` are the velocities of `x` and
`y` on a neighborhood of `t`.
