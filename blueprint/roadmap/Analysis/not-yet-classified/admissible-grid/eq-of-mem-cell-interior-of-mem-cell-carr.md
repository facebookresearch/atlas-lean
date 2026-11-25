# Eq of mem cell Interior of mem cell carrier

A point in one cell's open interior belongs to no other closed cell at the same scale.

```lean
theorem eq_of_mem_cellInterior_of_mem_cell_carrier (D : GridFilling)
    {u v : GridIndex} {z : ℂ} (hzv : z ∈ D.cellInterior v)
    (hzu : z ∈ (D.cell u).carrier) : u = v
```
