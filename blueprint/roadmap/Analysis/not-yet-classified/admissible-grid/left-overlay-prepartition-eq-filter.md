# Left Overlay Prepartition eq filter

The refined first filling is the global split restricted to its selected-cell union.

```lean
theorem leftOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.leftOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion
```
