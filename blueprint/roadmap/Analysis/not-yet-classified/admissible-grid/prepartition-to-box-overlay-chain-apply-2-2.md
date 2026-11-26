# Prepartition To Box Overlay Chain apply of not Mem

A nonmember box has integer coefficient zero in an unsigned prepartition chain.

```lean
theorem prepartitionToBoxOverlayChain_apply_of_notMem
    {B : BoxIntegral.Box (Fin 2)} {π : BoxIntegral.Prepartition B}
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∉ π) :
    prepartitionToBoxOverlayChain π I = 0
```
