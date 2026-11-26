# Point im

The imaginary vertex coordinate is its second integer coordinate divided by the filling scale.

```lean
theorem point_im (D : GridFilling) (v : GridIndex) :
    (D.point v).im = (v 1 : ℝ) / D.scale
```
