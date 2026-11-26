# Integral eq of have Common Filling Away From complex

The scalar contour integrals agree under the common-filling condition and complex
differentiability on `G \ K`.

```lean
theorem integral_eq_of_haveCommonFillingAwayFrom_complex
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → ℂ}
    (hD : D.reducedTrace ⊆ G \ K) (hE : E.reducedTrace ⊆ G \ K)
    (hDE : D.HaveCommonFillingAwayFrom E K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
```
