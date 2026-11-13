# Endpoint-honest reverse adapter

An integral curve of `sirField` on `[0, ∞)` gives a
solution of the SIR system provided it also has the two-sided derivative at `0`.

`IsIntegralCurveOn α _ (Ici 0)` only provides a right derivative at `0`, whereas `IsSolution`
asks for a two-sided derivative there; at every `t > 0` the set `Ici 0` is a neighbourhood of
`t` and the within-derivative is already two-sided. The hypothesis `h₀` cannot be dropped.
