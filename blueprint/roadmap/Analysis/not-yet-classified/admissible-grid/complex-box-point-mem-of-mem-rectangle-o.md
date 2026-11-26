# Complex Box Point mem of mem rectangle Of Box Interior

An open-rectangle point has its sign-reversed coordinate pair in the corresponding half-open
box.

```lean
theorem complexBoxPoint_mem_of_mem_rectangleOfBoxInterior
    (I : BoxIntegral.Box (Fin 2)) {z : ℂ}
    (hz : z ∈ rectangleOfBoxInterior I) : complexBoxPoint z ∈ I
```
