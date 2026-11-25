# Milnor Comparison comp matsumoto Reverse eq id

Conditional K₂-side inverse: if `ker toStableE = torusCocycleSubgroup` and
`matsumotoReverse` sends every algebraic Steinberg symbol to the Milnor symbol,
then `milnorComparison ∘ matsumotoReverse` is the identity on `Additive (K2 F)`.

Uses `K2_closure_steinbergSymbolProd_eq_top` for spanning and
`milnorComparison_k2Symbol` for the symbol-level computation. No stronger
generator theorem is assumed.
