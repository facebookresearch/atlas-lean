# Open Galois action

An open action of the absolute Galois group of `ℚ` on an additive
commutative group `M`, given by a monoid homomorphism into `AddAut M`
whose kernel is open for the Krull topology. Mathlib makes `AddAut M` an
additive group, so the homomorphism takes values in
`Multiplicative (AddAut M)`, as `DistribMulAction.toAddAut` does.
