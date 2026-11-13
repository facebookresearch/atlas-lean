# First-order bound for `exp x`

On the compact interval `|x| ≤ 1`,
`|exp x - (1 + x)| ≤ 3 / 4 * x ^ 2`. The constant `3 / 4` comes from Mathlib's `Real.exp_bound`
and is sharper than `1`. This is an inequality on that interval only, not an equality, and
nothing is asserted outside the interval.
