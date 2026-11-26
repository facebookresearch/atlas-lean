# Selected Filling cell carrier subset cthickening

For nonnegative radius, each selected closed cell lies in the closed `(2/t+r)`-thickening of
the compact set.

```lean
theorem selectedFilling_cell_carrier_subset_cthickening
    (K : Set ℂ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) (hK : IsCompact K)
    {v : GridIndex} (hv : v ∈ (selectedFilling K r t ht hK).cells) :
    ((selectedFilling K r t ht hK).cell v).carrier ⊆
      Metric.cthickening (2 / t + r) K
```
