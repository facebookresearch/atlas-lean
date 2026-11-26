# To Cycle integral

The cycle integral of a signed box chain is its finite integer-weighted sum of rectangle
boundary integrals.

```lean
theorem BoxOverlayChain.toCycle_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : BoxOverlayChain) (f : ℂ → E) :
    C.toCycle.integral f =
      C.sum fun I n ↦ n • (rectangleOfBox I).boundaryIntegral f
```
