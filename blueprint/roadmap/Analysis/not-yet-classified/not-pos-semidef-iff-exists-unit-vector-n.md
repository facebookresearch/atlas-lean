# Pos Semidef Unit Vector

A finite complex Hermitian matrix fails positive semidefiniteness exactly when its quadratic
form is a negative real value on some Euclidean unit vector. The unit normalization is the
coordinate sum of squared absolute values equal to one.

```lean
public theorem not_posSemidef_iff_exists_unitVector_neg {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    ¬ M.PosSemidef ↔ ∃ ψ : Complex.UnitVector n, star ψ.coord ⬝ᵥ (M *ᵥ ψ.coord) < 0
```
