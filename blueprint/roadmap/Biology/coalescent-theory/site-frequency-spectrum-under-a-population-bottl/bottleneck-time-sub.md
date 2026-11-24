# Increments of the bottleneck time change

For all real numbers `a`, `d`, `f`, `u` and `v`, the [time change](bottleneck-time.md) satisfies

`G(v) - G(u) = (v - u) - (1 - f) (O_{a,d/f}(v) - O_{a,d/f}(u))`,

where `O_{a,d/f}(u) = min(max(u - a, 0), d/f)` is the [clipped overlap expression](bottleneck-overlap.md)
with width `d/f` (with `d/0 = 0`). For `d/f ≥ 0` it is the length of the part of the window
`[a, a + d/f]` before `u`. For `d/f < 0` it equals `d/f` for every `u`, so the two terms cancel
and `G(v) - G(u) = v - u`.
