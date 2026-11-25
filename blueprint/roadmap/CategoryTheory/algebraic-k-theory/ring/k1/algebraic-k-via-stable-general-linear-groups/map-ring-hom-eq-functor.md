# Map Ring Hom eq functor

For rings `R, S : Type u` and a ring homomorphism `f : R →+* S`, the
coefficient map `mapRingHom f` equals the bundled additive homomorphism
`(K1.functor.map (RingCat.ofHom f)).hom : K1 R →+ K1 S`.
