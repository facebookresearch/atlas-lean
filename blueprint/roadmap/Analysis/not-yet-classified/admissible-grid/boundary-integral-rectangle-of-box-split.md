# Boundary Integral rectangle Of Box split

Rectangle boundary integration is additive under a coordinate split when
the integrand is globally continuous.

```lean
theorem boundaryIntegral_rectangleOfBox_split {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) (I : BoxIntegral.Box (Fin 2))
    (i : Fin 2) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
    (I.splitLower i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) +
      (I.splitUpper i x).elim' 0
        (fun J ↦ (rectangleOfBox J).boundaryIntegral f) =
      (rectangleOfBox I).boundaryIntegral f
```
