# Left Overlay Prepartition to Cycle integral

Subdivision of the first filling preserves the contour integral of a globally continuous
complete Banach-valued integrand.

```lean
theorem leftOverlayPrepartition_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (prepartitionToBoxOverlayChain (D.leftOverlayPrepartition E₁)).toCycle.integral f =
      D.toCycle.integral f
```
