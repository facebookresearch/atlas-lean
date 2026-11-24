# Compact Sheaf Source

The structural input. The compact-support sheaves, with the hom-groups inherited from all
sheaves, have finite products, kernels and cokernels, and every coimage-image comparison is an
isomorphism; the abelian structure below is built on the inherited preadditive structure. The
ind-sheaves carry an abelian structure (Kashiwara--Schapira, Categories and Sheaves,
Theorem 8.6.5(i)); Mathlib constructs it only for small categories and the compact-support sheaves
are not small, so it is recorded here. A category has at most one additive structure, so this datum
is determined up to propositional equality. Dependents are conditional on an instance; a
construction is requested in `WantedExt` (`IndSheafSourceRequests.actual_compact_sheaf_source`).
