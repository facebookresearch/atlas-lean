# Integral eq of is Admissible For

Admissible fillings for the same `K` and `G` have equal contour integrals of every complete
Banach-valued function complex differentiable on `G \ K`.

```lean
theorem integral_eq_of_isAdmissibleFor {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {D E : GridFilling} {K G : Set ℂ} {f : ℂ → F}
    (hD : D.IsAdmissibleFor K G) (hE : E.IsAdmissibleFor K G)
    (hf : DifferentiableOn ℂ f (G \ K)) :
    D.toCycle.integral f = E.toCycle.integral f
```
