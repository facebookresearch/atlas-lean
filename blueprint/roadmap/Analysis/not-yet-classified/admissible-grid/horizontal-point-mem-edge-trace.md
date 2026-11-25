# Horizontal point mem edge Trace

The complete stated horizontal coordinate interval belongs to the corresponding edge trace.

```lean
theorem horizontal_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {x : ℝ} (hx : x ∈ Icc ((v 0 : ℝ) / D.scale)
      (((v 0 : ℝ) + 1) / D.scale)) :
    (x : ℂ) + ((v 1 : ℝ) / D.scale : ℂ) * Complex.I ∈
      D.edgeTrace (.horizontal v)
```
