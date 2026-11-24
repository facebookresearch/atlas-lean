# Map Ring Hom

For rings `R : Type u` and `S : Type v`, a ring homomorphism `f : R →+* S`
induces an additive homomorphism `K1 R →+ K1 S` via the abelianization of
`StableGL.scalarMap f`. Unlike `K1.functor`, this map allows independent universes.
