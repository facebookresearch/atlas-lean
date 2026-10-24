---
article_id: af_952f43e00f92fc994433f054
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hadamard_zero_one_determinant_bound
---

# Hadamard Zero One Determinant Bound

Hadamard-derived determinant bound for arbitrary zero-one real matrices:
for every `{0,1}` matrix `B` of order `n`, `|det B| ≤ 2^(-n) (n+1)^((n+1)/2)`.

The source derives this by bordering and signing `2B` to obtain an
`(n+1) × (n+1)` sign matrix whose determinant is `2^n det B`, then applying
Hadamard's determinant inequality.

This is the sharper zero-one corollary, distinct from the already-proved
general row-norm theorem
`MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant.hadamard_determinant_inequality`
and from the Hadamard existence conjecture.
Proves `Wanted` entry `hadamard_zero_one_determinant_bound`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.HadamardZeroOneDeterminantBound](../../../../../sources/v2/MathlibExt.md)
- Richard P. Brent and Adam B. Yedidia, "Computation of Maximal Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21 (2018), Article 18.5.6. Stable source URL: https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex Exact statement lines 226–238. Verified source-file SHA-256: `c32c1f2e37c9fdaf1f56ccdbc9e257183500bf6ea6f64b819d8245d99cd676fd`. Verified span SHA-256: `92528b378d9b23e03d82114f91e804bb0774e4ed36aaa26e51b5f7fc501a5aaa`. Concept ID: `jis_grounded_381bade9817989f697266d6e`.
