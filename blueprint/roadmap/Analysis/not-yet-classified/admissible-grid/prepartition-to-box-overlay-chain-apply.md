# Prepartition To Box Overlay Chain apply

The unsigned box-chain coefficient is exactly the prepartition membership indicator.

```lean
theorem prepartitionToBoxOverlayChain_apply
    {B : BoxIntegral.Box (Fin 2)} (π : BoxIntegral.Prepartition B)
    (I : BoxIntegral.Box (Fin 2)) :
    prepartitionToBoxOverlayChain π I = prepartitionIndicator π I
```
