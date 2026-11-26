# Cell Multiplicity eq one iff

Multiplicity is one exactly when the floor-based owner cell is selected.

```lean
theorem cellMultiplicity_eq_one_iff (D : GridFilling) (z : ℂ) :
    D.cellMultiplicity z = 1 ↔ D.ownerIndex z ∈ D.cells
```
