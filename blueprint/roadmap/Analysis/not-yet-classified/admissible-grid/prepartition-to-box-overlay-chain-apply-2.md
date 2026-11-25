# Prepartition To Box Overlay Chain apply of mem

A member box has integer coefficient one in an unsigned prepartition chain.

```lean
theorem prepartitionToBoxOverlayChain_apply_of_mem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ π) :
    prepartitionToBoxOverlayChain π I = 1
```
