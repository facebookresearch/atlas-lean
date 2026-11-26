# Empty reduced Integral

Every complete Banach-valued reduced integral of an empty filling is zero.

```lean
theorem empty_reducedIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (t : ℝ) (ht : 0 < t) (f : ℂ → E) :
    (empty t ht).reducedIntegral f = 0
```
