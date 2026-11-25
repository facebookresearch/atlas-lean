# Spectral Pseudo Inverse mul spectral Pseudo Inverse

A Hermitian matrix satisfies the second Penrose equation `A† A A† = A†`.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralPseudoInverse_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralPseudoInverse A * A * spectralPseudoInverse A = spectralPseudoInverse A
```
