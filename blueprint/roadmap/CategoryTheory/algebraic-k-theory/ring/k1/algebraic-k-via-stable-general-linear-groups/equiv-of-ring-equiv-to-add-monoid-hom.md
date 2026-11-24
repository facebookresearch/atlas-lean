# Equiv Of Ring Equiv to Add Monoid Hom

For rings `R, S : Type u` and a ring equivalence `e : R ≃+* S`, the
bundled additive homomorphism `(K1.equivOfRingEquiv e).toAddMonoidHom : K1 R →+ K1 S`
equals `K1.mapRingHom e.toRingHom`.
