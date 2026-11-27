# Is Hermitian spectral Pseudo Inverse

The total spectral-pseudoinverse construction always yields a Hermitian matrix.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem isHermitian_spectralPseudoInverse (A : Matrix n n 𝕜) :
    (spectralPseudoInverse A).IsHermitian
```
