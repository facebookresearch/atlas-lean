# Index eq zero of not mem region

The analytic winding index is zero outside the selected-cell region.

```lean
theorem index_eq_zero_of_not_mem_region
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.region) :
    D.toCycle.index z = 0
```
