# Mem overlay Prepartition of mem common Overlay support

Every box with nonzero signed overlay coefficient lies in the global overlay partition.

```lean
theorem mem_overlayPrepartition_of_mem_commonOverlay_support
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ (D.commonOverlay E).support) :
    I ∈ D.overlayPrepartition E
```
