---
article_id: af_2b9c2cb34769d2c1b238cc7d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted.dft_inversion
---

# Dft inversion

Fourier inversion on a finite abelian group.

Proof: expand the transform and collapse the inner sum with the orthogonality of characters
from Mathlib's Pontryagin duality. This is the Fourier inversion formula (4.4) of K. Conrad,
Characters of finite abelian groups, Section 4,
https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, up to reindexing `ψ ↦ ψ⁻¹`
(Conrad conjugates the character in the transform rather than in the inversion sum).

## Depends on

- [Dft Fun](dft-fun.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FiniteAbelianDFT](../../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Fourier transform", entry "discrete Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2, Fourier inversion theorem.
