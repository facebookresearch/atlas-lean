# Prepartition To Box Overlay Chain to Cycle integral

An unsigned prepartition cycle integrates to the finite sum of its boxes' boundary integrals.

```lean
theorem prepartitionToBoxOverlayChain_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B) (f : ℂ → E) :
    (prepartitionToBoxOverlayChain π).toCycle.integral f =
      ∑ I ∈ π.boxes, (rectangleOfBox I).boundaryIntegral f
```
