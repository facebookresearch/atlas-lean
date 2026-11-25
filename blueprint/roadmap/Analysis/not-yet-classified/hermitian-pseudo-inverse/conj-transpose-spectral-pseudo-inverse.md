# Conj Transpose spectral Pseudo Inverse

Conjugate transpose fixes the spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem conjTranspose_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A)ᴴ = spectralPseudoInverse A
```
