# Dist le two div scale of mem cell carrier

Points in one closed cell have complex distance at most `2/D.scale`.

```lean
theorem dist_le_two_div_scale_of_mem_cell_carrier (D : GridFilling)
    (v : GridIndex) {z w : ℂ} (hz : z ∈ (D.cell v).carrier)
    (hw : w ∈ (D.cell v).carrier) : dist z w ≤ 2 / D.scale
```
