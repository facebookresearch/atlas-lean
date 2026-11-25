# Cdf mem Ioo of strict Mono

NEW OBLIGATION (helper for the roundtrips and for the endpoint
cases of `cdf_pushforward_eq_volume_restrict_Icc`).

Under a strictly monotone cdf of a probability measure, every cdf
value lies strictly between `0` and `1`: if `cdf μ x = 0`, any
`y < x` would have `cdf μ y < 0`; if `cdf μ x = 1`, any
`y > x` would
have `cdf μ y > 1`.  Continuity is not needed here.
