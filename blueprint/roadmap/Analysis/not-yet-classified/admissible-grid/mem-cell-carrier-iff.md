# Mem cell carrier iff

Closed-cell membership is exactly the pair of stated closed coordinate-interval conditions.

```lean
theorem mem_cell_carrier_iff (D : GridFilling) (v : GridIndex) (z : ℂ) :
    z ∈ (D.cell v).carrier ↔
      z.re ∈ Icc ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale) ∧
        z.im ∈ Icc ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)
```
