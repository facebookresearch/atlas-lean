# Termination for `e = 0`

For `g > 0` and `u₀ > 0` the first arc, with take-off speed
`u₀`, is the only active arc, and it ends at the positive time `2 u₀ / g`, the first and only
impact; as an active arc it is a ballistic flight that lands there with velocity `-u₀`
(`bounce_arc`). The ball then rests on the floor: every later take-off speed and flight duration
is `0`, so the elapsed time stays at `2 u₀ / g`; the later indices are rest, not further
impacts.
