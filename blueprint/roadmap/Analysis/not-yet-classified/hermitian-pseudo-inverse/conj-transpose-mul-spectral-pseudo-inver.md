# Conj Transpose mul spectral Pseudo Inverse

For Hermitian input, the product `A A†` is fixed by conjugate transpose.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.conjTranspose_mul_spectralPseudoInverse
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A * spectralPseudoInverse A)ᴴ = A * spectralPseudoInverse A
```
