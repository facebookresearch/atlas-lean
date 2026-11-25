# Functor map mk

For rings `R, S : Type u`, a ring homomorphism `f : R →+* S`, and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `K1.functor.map (RingCat.ofHom f)`
sends `K1.mk g` to `K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g)` in `K1 S`.
