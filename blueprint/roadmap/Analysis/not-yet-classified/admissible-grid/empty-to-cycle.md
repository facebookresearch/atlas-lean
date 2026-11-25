# Empty to Cycle

An empty positive-scale filling has the zero cycle.

```lean
theorem empty_toCycle (t : ℝ) (ht : 0 < t) :
    (empty t ht).toCycle = 0
```
