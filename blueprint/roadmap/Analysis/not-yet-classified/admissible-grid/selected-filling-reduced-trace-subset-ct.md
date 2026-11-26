# Selected Filling reduced Trace subset cthickening

For nonnegative radius, the reduced trace lies in the closed `(2/t+r)`-thickening.

```lean
theorem selectedFilling_reducedTrace_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K) :
    (selectedFilling K r t ht hK).reducedTrace ⊆
      Metric.cthickening (2 / t + r) K
```
