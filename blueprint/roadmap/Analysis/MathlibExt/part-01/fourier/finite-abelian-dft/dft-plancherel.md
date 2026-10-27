---
article_id: af_f813beb51119e2e534e2b600
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted.dft_plancherel
---

# Dft plancherel

Plancherel formula on a finite abelian group.

Proof: apply Fourier inversion to `g`, exchange the finite sums, and identify the conjugated
inner sum with `star (dftFun f ψ)`. Conrad (Section 4, cited above) proves the same identity by
checking it on characters.

## Depends on

- [Dft Fun](dft-fun.md)

## Proof depends on

- [Dft inversion](dft-inversion.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FiniteAbelianDFT](../../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Fourier transform", entry "discrete Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2, Plancherel formula.
