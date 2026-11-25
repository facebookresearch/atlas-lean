# Gen Map Fst

Functoriality preserves the generalized tuple entries.

Stable API for `powTupleGen`: mapping `f` through `monadPow` preserves every
tuple entry. By induction on `n` generalizing `X Y`: the zero case is a
subsingleton; the successor case exposes `Fin.snoc` on both sides, closes the
init components with the hypothesis at `T.obj`, and the last components with
`genMapSnd` (the tensor-monad map preserves the head factor). Consumed by the
later `ClassifyingNerveNaturality` repair instead of a local mirror.
