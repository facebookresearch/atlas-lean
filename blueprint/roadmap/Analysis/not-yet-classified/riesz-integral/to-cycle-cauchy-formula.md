# To Cycle cauchy formula

Cauchy's integral formula for a reduced grid contour whose filled region
lies in an open domain of differentiability.  The evaluation point is
required to lie off the reduced trace, where the Cauchy kernel is defined,
and the index-one hypothesis records the positive orientation.

```lean
theorem toCycle_cauchy_formula
    (D : GridFilling) {G : Set ℂ} (hG : IsOpen G) (hDG : D.region ⊆ G)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f G) {z : ℂ}
    (hzG : z ∈ G) (hztrace : z ∉ D.reducedTrace)
    (hindex : D.toCycle.index z = 1) :
    ((2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        D.toCycle.integral (fun ζ ↦ f ζ * (ζ - z)⁻¹) = f z
```
