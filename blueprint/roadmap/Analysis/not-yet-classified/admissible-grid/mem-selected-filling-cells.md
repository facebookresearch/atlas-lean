# Mem selected Filling cells

Membership in the constructed filling is exactly the prescribed cell-thickening intersection
condition.

```lean
theorem mem_selectedFilling_cells (K : Set ℂ) (r : ℝ) {t : ℝ}
    (ht : 0 < t) (hK : IsCompact K) (v : GridIndex) :
    v ∈ (selectedFilling K r t ht hK).cells ↔ v ∈ selectedCellSet K r t
```
