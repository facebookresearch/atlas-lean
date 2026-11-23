# Genomic control has type I error exactly α at a χ²₁ critical value

Consider a [common-inflation model](common-inflation-model.md) on a measure `P`, with inflation
factor `λ > 0` and null scores `Z_j`, each with law `𝒩(0, λ)` under `P`. Let `c` be a real
threshold with `P(χ²₁ > c) = α`, a level-`α` critical value of `χ²₁`. Then for every marker `j`,

`P(Z_j² / λ > c) = α`:

the genomic-control test that rejects marker `j` when `Z_j² / λ > c` has type I error exactly
`α`.
