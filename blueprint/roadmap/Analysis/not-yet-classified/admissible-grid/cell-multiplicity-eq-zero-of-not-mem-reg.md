# Cell Multiplicity eq zero of not mem region

Selected-cell multiplicity is zero outside the filling region.

```lean
theorem cellMultiplicity_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.cellMultiplicity z = 0
```
