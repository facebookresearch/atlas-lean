# An exact functor may be pulled out of a right derived functor

If `E` is additive and
preserves homology then `(F ⋙ E).rightDerived n ≅ F.rightDerived n ⋙ E`, naturally in the
object of `A`.

Both right derived functors are the chosen injective resolution followed by a functor on
homotopy categories and then homology; the comparison is `Functor.mapHomotopyCategoryCompIso`
followed by `mapHomotopyCategoryHomologyIso`.
