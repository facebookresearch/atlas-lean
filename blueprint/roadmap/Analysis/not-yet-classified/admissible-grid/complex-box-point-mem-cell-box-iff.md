# Complex Box Point mem cell Box iff

The sign-reversed coordinate pair lies in a half-open cell box exactly when that cell is the
floor-based owner.

```lean
theorem complexBoxPoint_mem_cellBox_iff (D : GridFilling)
    (v : GridIndex) (z : ℂ) :
    complexBoxPoint z ∈ D.cellBox v ↔ D.ownerIndex z = v
```
