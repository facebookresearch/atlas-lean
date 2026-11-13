# Wakefield's approximate Bayes factor

Wakefield's approximate Bayes factor: the `N(0, V + W)` density of the estimate `b` (its
marginal law under the alternative `β ~ N(0, W)`) divided by its `N(0, V)` density (the null
`β = 0`). Wakefield (2009) reports the reciprocal, null over alternative; coloc and SuSiE use
this orientation, in which large values favor association. For `V = 0` the null density is
Mathlib's junk value `0` and so is the ratio; the theorems assume `V ≠ 0`.
