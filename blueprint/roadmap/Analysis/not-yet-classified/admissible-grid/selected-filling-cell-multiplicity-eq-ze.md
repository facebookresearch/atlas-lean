# Selected Filling cell Multiplicity eq zero of not mem cthickening

For nonnegative radius, multiplicity is zero outside the closed `(2/t+r)`-thickening.

```lean
theorem selectedFilling_cellMultiplicity_eq_zero_of_not_mem_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {z : ℂ} (hz : z ∉ Metric.cthickening (2 / t + r) K) :
    (selectedFilling K r t ht hK).cellMultiplicity z = 0
```
