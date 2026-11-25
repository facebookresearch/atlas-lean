# Conj Transpose spectral Pseudo Inverse mul

For Hermitian input, the product `A† A` is fixed by conjugate transpose.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.conjTranspose_spectralPseudoInverse_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A
```
