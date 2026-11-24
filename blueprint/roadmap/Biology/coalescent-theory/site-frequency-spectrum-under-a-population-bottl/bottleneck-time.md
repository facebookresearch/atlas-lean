# Griffiths–Tavaré time change for a bottleneck

For real numbers `a`, `d`, `f` and `u`, let `G(u) = u - (1 - f) O_{a,d/f}(u)`, where
`O_{a,d/f}(u) = min(max(u - a, 0), d/f)` is the [clipped overlap expression](bottleneck-overlap.md)
with width `d/f`. For `d/f ≥ 0` it is the length of the part of the window `[a, a + d/f]` before
`u`, which equals `|[0, u] ∩ [a, a + d/f]|` when also `a ≥ 0`; for `d/f < 0` (for example
`d = -1` and `f = 2`) it equals `d/f` for every `u` and is not a length. With the convention
`d / 0 = 0`, at `f = 0` the width is `0`, the clipped expression is `0` and `G(u) = u`. The
intended parameters are `a ≥ 0`, `d ≥ 0` and `f > 0`.

For any real `a`, with `d ≥ 0` and `f > 0`, `G` is the inverse of the
[bottleneck intensity](bottleneck-rate.md) `R`:
[`R(G(u)) = u`](bottleneck-rate-bottleneck-time.md) and
[`G(R(s)) = s`](bottleneck-time-bottleneck-rate.md) for all real `u` and `s`. `G` is piecewise
affine, with slope `1` on `u < a` and on `u > a + d/f`, and slope `f` on `a < u < a + d/f` (an
empty interval when `d = 0`).

If moreover `a ≥ 0`, then [`G(0) = 0`](bottleneck-time-zero.md) and, for `s ≥ 0`, `R(s)` is the
[cumulative coalescence intensity](cum-rate-bottleneck-size.md) `∫_0^s dr / η(r)` of the
[bottleneck history](bottleneck-size.md) `η`. So for `u ≥ 0`, `G(u)` is the real time before the
present at which that intensity reaches `u`, and a standard-coalescent event at standard time
`u` happens at real time `G(u)`. For `a < 0` this reading can fail: with `a = -1`, `d = 1` and
`f = 1/2`, `η(s) = 1` for every `s ≥ 0`, yet `G(0) = -1/2`.
