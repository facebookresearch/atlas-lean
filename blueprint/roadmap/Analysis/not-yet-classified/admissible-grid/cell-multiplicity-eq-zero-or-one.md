# Cell Multiplicity eq zero or one

Selected-cell multiplicity is always zero or one.

```lean
theorem cellMultiplicity_eq_zero_or_one (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 0 ∨ D.cellMultiplicity z = 1
```
