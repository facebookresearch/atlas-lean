---
article_id: af_b7775adf963c2694099d13c6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.InnerProductSpace.CompactSpectralWanted.compactNormal_hilbertBasis
---

# Compact Spectral

A compact normal `T : E →L[ℂ] E` on a complex Hilbert space admits a Hilbert basis `b` with
eigenvalues `μ` vanishing at infinity and `T (b i) = μ i • b i`, with index type in the same
universe as `E`. Source: Compact normal spectral theorem, Hilbert-Schmidt and Riesz 1910s;
Reed-Simon I; Rudin Functional Analysis; Lean states complex Hilbert compact `IsStarNormal` case
with same finite-level-set vanishing condition and same-universe index.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.InnerProductSpace.CompactSpectral](../../../../../sources/v2/MathlibExt.md)
