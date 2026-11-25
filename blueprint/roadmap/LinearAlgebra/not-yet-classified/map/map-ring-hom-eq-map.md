# Map Ring Hom eq map

For commutative rings `R`, `S`, a finite index type `n` with decidable
equality, and a ring homomorphism `f : R →+* S`, `mapRingHom f` equals Mathlib's
`GeneralLinearGroup.map f` as a homomorphism `GL n R →* GL n S`. This comparison
requires commutative rings; the entrywise construction itself works for semirings.
