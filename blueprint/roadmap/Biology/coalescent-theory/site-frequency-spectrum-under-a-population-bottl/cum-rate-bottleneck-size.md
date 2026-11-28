# Cumulative coalescence intensity of the bottleneck history

For real numbers `a ≥ 0`, `d ≥ 0` and `s ≥ 0`, and every real `f`, the
[cumulative coalescence intensity](../site-frequency-spectrum-under-variable-populatio/cum-rate.md)
of the [bottleneck history](bottleneck-size.md) `η` is

`R_η(s) = ∫_0^s dr / η(r) = s + (1/f - 1) |[0, s] ∩ [a, a + d]|`,

the [piecewise-linear intensity](bottleneck-rate.md) `R(s)`, where
`|[0, s] ∩ [a, a + d]| = min(max(s - a, 0), d)`. Both sides use the convention `1/0 = 0`: at
`f = 0` both equal `s - |[0, s] ∩ [a, a + d]|`.
