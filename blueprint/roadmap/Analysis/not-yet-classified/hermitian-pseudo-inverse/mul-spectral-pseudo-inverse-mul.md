# Mul spectral Pseudo Inverse mul

A Hermitian matrix satisfies the first Penrose equation `A A† A = A`.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem IsHermitian.mul_spectralPseudoInverse_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A * spectralPseudoInverse A * A = A
```
