# Functor map proj

For rings `R, S : Type u`, a ring homomorphism `f : R →+* S`, and `g : StableGL R`,
`K1.functor.map (RingCat.ofHom f)` sends `K1.proj g` to the projection
of `(StableGL.functor.map (SemiRingCat.ofHom f)) g` in `K1 S`.
