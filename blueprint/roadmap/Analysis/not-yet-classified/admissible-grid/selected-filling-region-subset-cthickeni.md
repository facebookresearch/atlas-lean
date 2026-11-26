# Selected Filling region subset cthickening

For nonnegative radius, the full selected-cell region lies in the same closed
`(2/t+r)`-thickening.

```lean
theorem selectedFilling_region_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).region ⊆ Metric.cthickening (2 / t + r) K
```
