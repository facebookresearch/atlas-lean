# Conj Transpose spectral Support

Conjugate transpose fixes the spectral support.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem conjTranspose_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A)ᴴ = spectralSupport A
```
