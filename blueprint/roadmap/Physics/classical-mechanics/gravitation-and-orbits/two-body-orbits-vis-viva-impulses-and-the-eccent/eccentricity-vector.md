# Eccentricity Vector

Eccentricity vector `e = (v ⨯₃ h) / μ - x / r` of the state `(x, v)`, with `h = x ⨯₃ v` the
specific angular momentum and `r = |x|`. Declared for `μ > 0` and `r > 0`; at `x = 0` or `μ = 0`
Lean's convention `1 / 0 = 0` gives a meaningless value.
