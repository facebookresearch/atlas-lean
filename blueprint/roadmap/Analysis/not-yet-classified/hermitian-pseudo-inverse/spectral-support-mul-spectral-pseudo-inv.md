# Spectral Support mul spectral Pseudo Inverse

The spectral support acts as the identity on the spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_mul_spectralPseudoInverse (A : Matrix n n 𝕜) :
    spectralSupport A * spectralPseudoInverse A = spectralPseudoInverse A
```
