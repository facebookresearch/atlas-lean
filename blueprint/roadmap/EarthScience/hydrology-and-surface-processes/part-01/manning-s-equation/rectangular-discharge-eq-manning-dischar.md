# Rectangular discharge as a Manning discharge

For all real `n`, `S`, `b` and `h`, the rectangular-channel discharge with prefactor `√S / n` is
the Manning discharge at flow area `b * h` and hydraulic radius `r = (b * h) / (b + 2 * h)`:
`(√S / n) * (b * h) * r ^ (2 / 3) = (1 / n) * (b * h) * r ^ (2 / 3) * √S`. The identity covers every
real input: with the conventions `√x = 0` for `x < 0`, `x / 0 = 0` and `x ^ y = |x| ^ y * cos (π y)`
for `x < 0`, both sides are `0` when `S ≤ 0`, `n = 0` or `b + 2 * h = 0`, and a negative `r` enters
both sides as `r ^ (2 / 3) = -|r| ^ (2 / 3) / 2`.

In the hydraulic reading, `n > 0` is the roughness coefficient, `S ≥ 0` the bed slope, and `b > 0`
and `h > 0` the channel width and flow depth, so that `b + 2 * h > 0` and `r > 0`; the identity
holds more generally for all real inputs, with the values above.
