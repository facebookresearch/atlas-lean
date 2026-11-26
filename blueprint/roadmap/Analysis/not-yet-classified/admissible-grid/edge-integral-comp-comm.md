# Edge Integral comp comm

A continuous complex-linear map commutes with an edge integral when the integrand is continuous
on that edge.

```lean
theorem edgeIntegral_comp_comm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (D : GridFilling) (e : GridEdge) (L : E →L[ℂ] F) (f : ℂ → E)
    (hf : ContinuousOn f (D.edgeTrace e)) :
    D.edgeIntegral e (fun z ↦ L (f z)) = L (D.edgeIntegral e f)
```
