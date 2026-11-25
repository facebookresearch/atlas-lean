# Spectral Pseudo Inverse penrose

The computed spectral reciprocal of a finite Hermitian matrix satisfies all four Moore–Penrose
equations.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_penrose {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A ∧
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A ∧
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A ∧
    (spectralPseudoInverse A * A)ᴴ = spectralPseudoInverse A * A
```
