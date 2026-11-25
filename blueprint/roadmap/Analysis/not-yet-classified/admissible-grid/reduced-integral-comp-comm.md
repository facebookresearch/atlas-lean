# Reduced Integral comp comm

A continuous complex-linear map commutes with the reduced integral when the integrand is
continuous on a containing set.

```lean
theorem reducedIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (L : E →L[ℂ] F) (f : ℂ → E)
    {U : Set ℂ} (hD : D.reducedTrace ⊆ U) (hf : ContinuousOn f U) :
    D.reducedIntegral (fun z ↦ L (f z)) = L (D.reducedIntegral f)
```
