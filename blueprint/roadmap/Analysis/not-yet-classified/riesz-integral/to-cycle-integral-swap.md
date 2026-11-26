# To Cycle integral swap

Fubini's theorem for two reduced rectilinear grid contours.  The order
of the two arguments of `F` is unchanged, so the result applies to functions
with values in a noncommutative Banach algebra.

```lean
theorem toCycle_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D H : GridFilling) (F : ℂ → ℂ → E)
    (hF : ContinuousOn (Function.uncurry F)
      (D.reducedTrace ×ˢ H.reducedTrace)) :
    D.toCycle.integral (fun z ↦ H.toCycle.integral (F z)) =
      H.toCycle.integral (fun ζ ↦ D.toCycle.integral (fun z ↦ F z ζ))
```
