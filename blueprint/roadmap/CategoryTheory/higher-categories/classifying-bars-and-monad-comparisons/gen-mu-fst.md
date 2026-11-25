# Gen Mu Fst

`muAtPos` multiplies the generalized adjacent tuple entries.

By induction on `n`: the zero case is vacuous; the `⟨0⟩` case multiplies the
last pair (pointwise in the result index: below via `genMapFst`, at via
`muApp_head`); the `⟨jv+1⟩` case peels one `powTupleGen_succ_fst` layer on
each side, rewrites the snoc structure with `tupleMulAt_snoc`, and closes
the init components with the hypothesis and the last components with
`genMuSnd`. The `muAtPos` index `j` (from the innermost end) corresponds to
tuple position `n - 1 - j.val` (from the outermost end).
