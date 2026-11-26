# Empty region

The region of an empty filling is empty.

```lean
theorem empty_region (t : ℝ) (ht : 0 < t) :
    (empty t ht).region = ∅
```
