# Is Noetherian Object iff finite

Over a noetherian ring, finite generation is exactly the categorical noetherian-object
property in `ModuleCat R`. The proof combines `isNoetherianObject_iff_isNoetherian` with the
algebraic facts `IsNoetherian R M → Module.Finite R M` and
`[IsNoetherianRing R] [Module.Finite R M] → IsNoetherian R M`.
