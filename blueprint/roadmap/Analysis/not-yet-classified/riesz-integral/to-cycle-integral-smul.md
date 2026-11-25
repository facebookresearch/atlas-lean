# To Cycle integral smul

A fixed reduced grid contour commutes with complex scalar multiplication
of a Banach-valued integrand continuous on the contour.

```lean
theorem toCycle_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling) (c : ℂ)
    (f : ℂ → E) (hf : ContinuousOn f D.reducedTrace) :
    D.toCycle.integral (c • f) = c • D.toCycle.integral f
```
