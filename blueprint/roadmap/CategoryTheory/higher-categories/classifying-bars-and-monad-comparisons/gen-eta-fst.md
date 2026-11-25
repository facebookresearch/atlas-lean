# Gen Eta Fst

`etaAtPos` inserts `1` into the generalized tuple.

By induction on `n`: the zero case is a single `snoc` with `etaApp_head`;
the `⟨0⟩` case inserts at the last position (pointwise in the result index:
below via `genMapFst`, at via `etaApp_head`); the `⟨jv+1⟩` case peels one
`powTupleGen_succ_fst` layer on each side, rewrites the snoc structure with
`tupleInsAt_snoc`, and closes the init components with the hypothesis and
the last components with `genEtaSnd`. The `etaAtPos` index `j` (from the
innermost end) corresponds to tuple position `n - j.val` (from the
outermost end).
