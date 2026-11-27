# Is Hermitian spectral Support

The total spectral-support construction always yields a Hermitian matrix.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem isHermitian_spectralSupport (A : Matrix n n 𝕜) :
    (spectralSupport A).IsHermitian
```
