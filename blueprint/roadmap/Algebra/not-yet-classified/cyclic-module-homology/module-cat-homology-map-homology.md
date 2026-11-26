# Module Cat homology Map homologyπ

Homology maps commute with the class map from cycles, on elements of complexes of modules.

Not `@[simp]`: it would make the existing simp lemmas
`ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply` and
`TopCat.singularCohomologyMap_homologyπ_constSingularCocycle` fail `simpNF`.
