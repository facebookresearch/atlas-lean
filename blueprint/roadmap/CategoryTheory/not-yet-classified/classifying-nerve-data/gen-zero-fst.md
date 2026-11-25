# Gen Zero Fst

Iterated right action drops the generalized head tuple entry.

By induction on `n` generalizing `X`: the zero case is a subsingleton;
the successor case exposes `Fin.snoc` on both sides (via
`powTupleGen_succ_fst`), commutes `Fin.tail` past `Fin.snoc`, and closes
the init components with the induction hypothesis and the last components
with `genZeroSnd` at `T.obj X`.
