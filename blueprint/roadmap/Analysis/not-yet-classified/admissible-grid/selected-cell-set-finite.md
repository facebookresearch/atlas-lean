# Selected Cell Set finite

At positive scale, the cells meeting a closed thickening of a compact planar set form a finite
set.

```lean
theorem selectedCellSet_finite (K : Set ℂ) (r : ℝ) {t : ℝ} (ht : 0 < t)
    (hK : IsCompact K) : (selectedCellSet K r t).Finite
```
