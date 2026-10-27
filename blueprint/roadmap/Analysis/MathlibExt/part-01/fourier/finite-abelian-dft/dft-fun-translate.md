---
article_id: af_f5bb6796a907e1aefd41b859
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted.dftFun_translate
---

# Dft Fun translate

Translation of the input modulates the Fourier transform by the character.

Proof: reindex the finite sum by `x ↦ x + t` and use character additivity.

## Depends on

- [Dft Fun](dft-fun.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FiniteAbelianDFT](../../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Fourier transform", entry "discrete Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2 (translation and modulation).
