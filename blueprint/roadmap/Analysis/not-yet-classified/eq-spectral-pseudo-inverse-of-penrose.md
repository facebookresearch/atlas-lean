# Hermitian Pseudo Inverse Unique

For a finite Hermitian input `A`, any matrix `X` satisfying both Penrose product equations and
Hermitianity of `AX` and `XA` equals the computed spectral pseudoinverse.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem eq_spectralPseudoInverse_of_penrose {A X : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hAXA : A * X * A = A) (hXAX : X * A * X = X)
    (hAX : (A * X).IsHermitian) (hXA : (X * A).IsHermitian) :
    X = spectralPseudoInverse A
```
