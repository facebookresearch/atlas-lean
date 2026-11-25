# To Cycle integral add

A fixed reduced grid contour is additive in a Banach-valued integrand
that is continuous on the contour.

```lean
theorem toCycle_integral_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : GridFilling)
    {f g : ℂ → E} (hf : ContinuousOn f D.reducedTrace)
    (hg : ContinuousOn g D.reducedTrace) :
    D.toCycle.integral (f + g) =
      D.toCycle.integral f + D.toCycle.integral g
```
