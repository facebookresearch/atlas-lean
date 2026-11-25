# Angular Sublevel Set subset

Every angular sublevel set lies in the full-period interval `(0,2π]`.

```lean
theorem angularSublevelSet_subset (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelSet u r K ⊆ Set.Ioc 0 (2 * Real.pi)
```
