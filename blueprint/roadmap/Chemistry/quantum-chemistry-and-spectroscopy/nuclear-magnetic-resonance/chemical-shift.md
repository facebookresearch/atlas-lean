# Chemical Shift

Chemical shift in ppm: `δ = 1e6 * (ν - νref) / νref`, a dimensionless
ratio of frequencies in Hz. `1e6` is the real literal `1000000`. The shift is
defined only for a reference frequency `νref ≠ 0`: at `νref = 0` Lean's
convention `x / 0 = 0` gives the meaningless value `0`, and the lemmas below
assume `νref ≠ 0` (or a shielding model with `νref ≠ 0`).
