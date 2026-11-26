# Point re

The real vertex coordinate is its first integer coordinate divided by the filling scale.

```lean
theorem point_re (D : GridFilling) (v : GridIndex) :
    (D.point v).re = (v 0 : ℝ) / D.scale
```
