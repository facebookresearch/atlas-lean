# Monoidal scalar restriction along a ring equivalence

For commutative rings `R,S : Type s` and a ring equivalence `e : R ≃+* S`, the
restriction-of-scalars functor `F=ModuleCat.restrictScalars e.toRingHom` is monoidal. The
structure uses its lax unit and tensor maps, with inverses supplied by the ring-equivalence
unit and balanced tensor comparisons.
