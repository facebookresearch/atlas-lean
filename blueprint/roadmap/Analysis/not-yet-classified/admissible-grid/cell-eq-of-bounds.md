# Cell eq of Bounds

A cell is the closed rectangle between its successive scaled integer coordinates.

```lean
theorem cell_eq_ofBounds (D : GridFilling) (v : GridIndex) :
    D.cell v = RectilinearRectangle.ofBounds
      ((v 0 : ℝ) / D.scale) (((v 0 : ℝ) + 1) / D.scale)
      ((v 1 : ℝ) / D.scale) (((v 1 : ℝ) + 1) / D.scale)
```
