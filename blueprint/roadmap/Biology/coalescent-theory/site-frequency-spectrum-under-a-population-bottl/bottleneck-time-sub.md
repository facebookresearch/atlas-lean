# Increments of the bottleneck time change

For all real numbers `a`, `d`, `f`, `u` and `v`, the [time change](bottleneck-time.md) satisfies

`G(v) - G(u) = (v - u) - (1 - f) (O_{a,d/f}(v) - O_{a,d/f}(u))`,

where `O_{a,d/f}(u) = min(max(u - a, 0), d/f)` is the [overlap](bottleneck-overlap.md) of the
window `[a, a + d/f]` with the times before `u` (with `d/0 = 0`).
