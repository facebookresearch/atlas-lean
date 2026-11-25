# To Cycle sub

Taking rectangle boundaries sends subtraction of signed box chains to subtraction of cycles.

```lean
theorem BoxOverlayChain.toCycle_sub (C D : BoxOverlayChain) :
    (C - D).toCycle = C.toCycle - D.toCycle
```
