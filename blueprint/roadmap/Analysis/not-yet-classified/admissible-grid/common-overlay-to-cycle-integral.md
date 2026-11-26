# Common Overlay to Cycle integral

For a globally continuous complete Banach-valued integrand, the signed overlay integral is the
difference of the filling integrals.

```lean
theorem commonOverlay_toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D E₁ : GridFilling) (f : ℂ → E) (hf : Continuous f) :
    (D.commonOverlay E₁).toCycle.integral f =
      D.toCycle.integral f - E₁.toCycle.integral f
```
