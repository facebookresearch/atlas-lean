# To Cycle index eq cell Coeff of mem cell Interior

At an interior point of a grid cell, the filling-cycle index is that cell's selected indicator
coerced to a complex number.

```lean
theorem toCycle_index_eq_cellCoeff_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    D.toCycle.index z = (D.cellCoeff v : ℂ)
```
