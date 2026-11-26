# Full Substitution

Full elementwise substitution: apply `O.subst` at `substitutionData I J`
to the `Option`-indexed family `none ↦ outer`, `some i ↦ inner i`.
Supports empty `I` and empty `J i` with no `Nonempty` assumptions.
