# Mul spectral Pseudo Inverse eq spectral Support

On each nonzero eigenspace, multiplication by the spectral reciprocal
cancels the eigenvalue; the zero eigenspace is annihilated.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.mul_spectralPseudoInverse_eq_spectralSupport
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A = spectralSupport A
```
