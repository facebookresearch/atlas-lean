# Subst App

Lexicographic substitution for the associative collection.

For `X : SubstitutionData`, an element of the source is an `Option`-indexed
family `fam` where `fam none` is the outer order on `X.index` and
`fam (some i)` is the inner order on `(X.obj i).of`. The map installs
`fam none` as `LinearOrder X.index` and `fam (some i)` as
`LinearOrder (X.obj i).of`, then returns the inferred Mathlib lexicographic
`LinearOrder` on the dependent sum `(a : X.index) × (X.obj a).of`.
