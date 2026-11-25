# Empty boundary Edges

An empty positive-scale filling has no reduced boundary edges.

```lean
theorem empty_boundaryEdges (t : ℝ) (ht : 0 < t) :
    (empty t ht).boundaryEdges = ∅
```
