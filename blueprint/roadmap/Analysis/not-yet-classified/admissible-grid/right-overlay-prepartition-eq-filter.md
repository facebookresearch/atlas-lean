# Right Overlay Prepartition eq filter

The refined second filling is the global split restricted to its selected-cell union.

```lean
theorem rightOverlayPrepartition_eq_filter (D E : GridFilling) :
    D.rightOverlayPrepartition E =
      (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
        (D.overlayHyperplanes E)).filter
          fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion
```
