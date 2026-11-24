# Restrict Scalars

Restriction of scalars for finitely generated modules along a finite ring homomorphism
`f : R →+* S`. On objects it sends a finite `S`-module `M` to the `R`-module obtained by
`Module.compHom M f`; finiteness over `R` follows from `S` being finite over `R` and
`M` finite over `S` via `Module.Finite.trans`.
