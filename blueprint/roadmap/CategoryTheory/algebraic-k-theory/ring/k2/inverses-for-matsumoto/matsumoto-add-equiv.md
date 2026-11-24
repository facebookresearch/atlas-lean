# Matsumoto Add Equiv

Conditional Matsumoto additive equivalence `MilnorK F 2 ≃+ Additive (K2 F)`.

Forward map is the existing `milnorComparison F`; inverse is `matsumotoReverse F`.
This is conditional on the symbol bridge
`∀ a b, matsumotoReverse (steinbergSymbol a b) = k2Symbol a b` and on
`MonoidHom.ker (StableSteinberg.toStableE (R := F)) = torusCocycleSubgroup`.
No unconditional Matsumoto isomorphism is established in this file.
