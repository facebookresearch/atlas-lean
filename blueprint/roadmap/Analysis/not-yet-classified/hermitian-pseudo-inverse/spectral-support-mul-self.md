# Spectral Support mul self

The spectral support is idempotent for every matrix input, including the total-CFC zero case.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_mul_self (A : Matrix n n 𝕜) :
    spectralSupport A * spectralSupport A = spectralSupport A
```
