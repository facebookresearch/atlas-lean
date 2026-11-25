# Empty cells

An empty positive-scale filling has no selected cells.

```lean
theorem empty_cells (t : ℝ) (ht : 0 < t) : (empty t ht).cells = ∅
```
