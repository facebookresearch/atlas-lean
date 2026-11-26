# Scalar restriction preserves homology

For commutative rings `R : Type u`, `S : Type w` with `Algebra R S`, the functor
`ModuleCat.restrictScalars (algebraMap R S) : ModuleCat.{v} S → ModuleCat.{v} R` preserves
homology. The ring and module-carrier universes are independent.
