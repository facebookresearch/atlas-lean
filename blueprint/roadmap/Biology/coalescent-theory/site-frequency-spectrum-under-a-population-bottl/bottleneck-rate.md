# Piecewise-linear intensity of the bottleneck history

For real numbers `a`, `d`, `f` and `s`, let `R(s) = s + (1/f - 1) O_{a,d}(s)`, where
`O_{a,d}(s) = min(max(s - a, 0), d)` is the [clipped overlap expression](bottleneck-overlap.md)
with width `d`. For `d ≥ 0` it is the length of the part of the window `[a, a + d]` before `s`;
for `d < 0` it equals `d` for every `s` and is not a length. With the convention `0⁻¹ = 0`, the
factor `1/f` is `0` at `f = 0`, where `R(s) = s - O_{a,d}(s)`. The intended parameters are
`a ≥ 0`, `d ≥ 0` and `f > 0`. For `a, d, s ≥ 0` (and every real `f`),
`O_{a,d}(s) = |[0, s] ∩ [a, a + d]|` and `R(s)` is the
[cumulative coalescence intensity](cum-rate-bottleneck-size.md) `∫_0^s dr / η(r)` of the
[bottleneck history](bottleneck-size.md) `η`.
