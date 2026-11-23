# The upwind update is monotone under the CFL condition

For viscosities `μo > 0` and `μw > 0` and a CFL number `ν` with `0 ≤ ν * B ≤ 1`, where
`B = (μo + μw) ^ 2 / (2 * μo * μw)` is the [derivative bound](frac-flow-bound.md), the
[upwind update](upwind-update.md) `a - ν * (f(a) - f(b))` is nondecreasing in the cell state `a`
and in the upwind state `b` on `[0, 1]`: for `a ≤ a'` and `b ≤ b'` in `[0, 1]`, the update at
`(a, b)` is at most the update at `(a', b')`.
