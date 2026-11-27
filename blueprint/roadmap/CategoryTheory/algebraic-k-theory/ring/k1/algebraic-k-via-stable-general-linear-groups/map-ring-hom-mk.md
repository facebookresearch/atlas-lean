# Map Ring Hom mk

For a ring homomorphism `f : R →+* S` between rings in independent universes and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `mapRingHom f` sends `K1.mk g` to
`K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g)`.
