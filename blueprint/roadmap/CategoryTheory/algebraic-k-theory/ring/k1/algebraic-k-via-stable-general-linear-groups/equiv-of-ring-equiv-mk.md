# Equiv Of Ring Equiv mk

For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `K1.equivOfRingEquiv e (K1.mk g)`
equals `K1.mk (Matrix.GeneralLinearGroup.mapRingHom e.toRingHom g)` in `K1 S`.
