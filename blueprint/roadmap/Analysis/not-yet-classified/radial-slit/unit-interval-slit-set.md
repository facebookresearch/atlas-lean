# Unit Interval slit Set

The distinguished slit is exactly the complex real-axis segment `[0,1]`.

```lean
theorem unitInterval_slitSet :
    unitInterval.slitSet = Set.Icc 0 1 ×ℂ ({0} : Set ℝ)
```
