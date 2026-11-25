# Spectral Support mul

For a Hermitian input, its support acts as the identity on that input.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.spectralSupport_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    spectralSupport A * A = A
```
