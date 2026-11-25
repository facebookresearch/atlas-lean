# Gen Map Snd

Functoriality preserves the generalized base point up to `f`.

Stable API for `powTupleGen`: mapping `f` through `monadPow` acts as `f` on
the base point. By induction on `n` generalizing `X Y`: the zero case is a
cast roundtrip; the successor case peels `powTupleGen_succ_snd` on both sides
and applies the hypothesis at `T.obj`, since `(monadPow (n+1)).map f =
(monadPow n).map (T.map f)` definitionally. Consumed by the later
`ClassifyingNerveNaturality` repair instead of a local mirror.
