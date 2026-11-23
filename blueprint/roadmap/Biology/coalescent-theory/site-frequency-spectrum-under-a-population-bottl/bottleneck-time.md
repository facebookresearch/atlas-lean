# Griffiths–Tavaré time change for a bottleneck

For real numbers `a`, `d`, `f` and `u`, let `G(u) = u - (1 - f) O_{a,d/f}(u)`, where
`O_{a,d/f}(u) = min(max(u - a, 0), d/f)` is the [overlap](bottleneck-overlap.md) of the window
`[a, a + d/f]` with the times before `u`; it equals `|[0, u] ∩ [a, a + d/f]|` when `a ≥ 0`,
`d ≥ 0` and `f > 0`. The intended parameters are `a ≥ 0`, `d ≥ 0` and `f > 0`. With the
convention `d / 0 = 0`, at `f = 0` the window has length `0` and `G(u) = u`.

For `d ≥ 0` and `f > 0` (and every real `a`), `G` is the inverse of the
[bottleneck intensity](bottleneck-rate.md) `R`:
[`R(G(u)) = u`](bottleneck-rate-bottleneck-time.md) and
[`G(R(s)) = s`](bottleneck-time-bottleneck-rate.md) for all real `u` and `s`. So `G(u)` is the
real time at which `R` reaches `u`, and a standard-coalescent event at standard time `u` happens
at real time `G(u)`. The function `G` has slope `1` outside the window `[a, a + d/f]` and slope
`f` on it.
