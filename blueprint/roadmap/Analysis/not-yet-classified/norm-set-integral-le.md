# Local L2 Bound

A scalar L2 set integral on a measurable finite-measure set is bounded by the square root of
that set measure times the original L2 norm.

```lean
theorem norm_setIntegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (f : Lp ℂ 2 μ) :
    ‖∫ x in s, f x ∂μ‖ ≤ μ.real s ^ (1 / 2 : ℝ) * ‖f‖
```
