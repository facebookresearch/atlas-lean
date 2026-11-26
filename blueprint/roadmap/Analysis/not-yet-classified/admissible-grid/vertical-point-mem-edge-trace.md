# Vertical point mem edge Trace

The complete stated vertical coordinate interval belongs to the corresponding edge trace.

```lean
theorem vertical_point_mem_edgeTrace (D : GridFilling) (v : GridIndex)
    {y : ℝ} (hy : y ∈ Icc ((v 1 : ℝ) / D.scale)
      (((v 1 : ℝ) + 1) / D.scale)) :
    ((v 0 : ℝ) / D.scale : ℂ) + (y : ℂ) * Complex.I ∈
      D.edgeTrace (.vertical v)
```
