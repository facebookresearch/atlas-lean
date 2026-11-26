# Agreement with Mathlib's tangent slope

Over a field, if $2y + a_1x + a_3 \ne 0$, then
`W.tangentSlope x y` equals `W.toAffine.slope x x y y`.
