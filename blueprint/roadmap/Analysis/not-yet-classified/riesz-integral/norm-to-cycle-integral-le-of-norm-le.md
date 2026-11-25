# Norm to Cycle integral le of norm le

Norm bound for a Banach-valued integral along a reduced grid boundary.
The factor before `C` is exactly the total length of the surviving grid
edges.

```lean
theorem norm_toCycle_integral_le_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {f : ℂ → E} {C : ℝ}
    (hf : ∀ z ∈ D.reducedTrace, ‖f z‖ ≤ C) :
    ‖D.toCycle.integral f‖ ≤
      ((D.boundaryEdges.card : ℝ) / D.scale) * C
```
