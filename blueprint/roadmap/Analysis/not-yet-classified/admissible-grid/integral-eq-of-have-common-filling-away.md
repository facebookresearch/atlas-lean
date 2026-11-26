# Integral eq of have Common Filling Away From

Finite-overlay/common-refinement theorem.  Multiplicity-difference
support inside `G \ K`, together with the two reduced traces there, implies
equality of Banach-valued contour integrals for every function complex
differentiable on `G \ K`.

```lean
theorem integral_eq_of_haveCommonFillingAwayFrom {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
```
