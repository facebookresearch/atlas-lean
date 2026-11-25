# Right Overlay Prepartition to Cycle integral

Subdivision of the second filling preserves the contour integral of a globally continuous
complete Banach-valued integrand.

```lean
theorem rightOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.rightOverlayPrepartition E₁)).toCycle.integral f =
      E₁.toCycle.integral f
```
