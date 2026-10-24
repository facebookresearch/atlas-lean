---
article_id: af_a0548c5d157788c024df6e15
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsToeplitzMatrix
---

# Is Toeplitz Matrix

Toeplitz matrix, JIS VOL18/Felsner `felsner2.tex`, lines 271-283, Definition
(Toeplitz matrix): a real `(n + 1)` by `(n + 1)` matrix `A = (aᵢⱼ)` is Toeplitz
iff there exist real coefficients `c₋ₙ, …, cₙ` such that `aᵢⱼ = cᵢ₋ⱼ` for all
indices (equivalently, `A` is constant on every diagonal).

The witness `c` is total on `ℤ`; only the offsets in `[-n, n]` are observed.

Concept id: `jis_term_af166143477154e55b2be88d`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.Toeplitz](../../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex Source SHA-256: `f9b167508df14b8b3fa97556d04b3fd2fca3fc7939a1c23904e576e73f0a58c2`. Definition block SHA-256: `17bf8967c8c4965db527869b4efe74d630e63681258d740ad2f98a54e2ed8008`.
