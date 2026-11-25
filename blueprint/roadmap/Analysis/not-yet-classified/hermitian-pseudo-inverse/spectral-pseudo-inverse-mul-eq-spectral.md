# Spectral Pseudo Inverse mul eq spectral Support

For a Hermitian matrix, right multiplication by the input after its spectral pseudoinverse
gives the spectral support.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_mul_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A = spectralSupport A
```
