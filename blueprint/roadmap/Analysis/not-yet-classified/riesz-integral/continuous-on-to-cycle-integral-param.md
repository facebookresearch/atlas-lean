# Continuous On to Cycle integral param

Integrating one variable of a jointly continuous Banach-valued function
along a fixed reduced grid contour gives a function continuous in the other
variable.

```lean
theorem continuousOn_toCycle_integral_param
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) {S : Set ℂ} (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ D.reducedTrace)) :
    ContinuousOn (fun z ↦ D.toCycle.integral (F z)) S
```
