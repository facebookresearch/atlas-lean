# Equiv Of Ring Equiv proj

For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and `g : StableGL R`,
`K1.equivOfRingEquiv e` sends `K1.proj g` to `K1.proj` applied to the image of `g`
under `StableGL.functor.map (SemiRingCat.ofHom e.toRingHom)` in `StableGL S`.
