# Chain Complex Free Iso ULift

The degree-`n` object of the native simplicial chain complex with
universe-lifted coefficients is the free `R`-module on the `n`-simplices of
`X`.

The `ULift` coefficient object really belongs to
`ModuleCat.{max u w} R`; the resulting Finsupp coefficients are lowered back
to `R` through `ULift.moduleEquiv`.
