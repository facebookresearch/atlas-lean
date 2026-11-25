# Pow Tuple Gen

X-generalized head-first power reader.

`((monadPow (tensorMonad G) n).obj X)` is the left-nested product
`G × (G × ... × X)`; this reads it as `(Fin n → G) × X` with `t 0` the
outermost factor. Both defining equalities are `rfl`: `monadPow_succ` gives
`(monadPow (n+1)).obj X = (monadPow n).obj (T.obj X)` and `T.obj X = G × X`
in `Type`, so the successor step recurses at `T.obj X` and reassociates
`(init, (last, x))` to `(snoc init last, x)`.
