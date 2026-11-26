# Empty reduced Trace

The reduced trace of an empty filling is empty.

```lean
theorem empty_reducedTrace (t : ℝ) (ht : 0 < t) :
    (empty t ht).reducedTrace = ∅
```
