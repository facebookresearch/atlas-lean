# Overlay Hyperplanes spec

The chosen coordinate cuts satisfy the simultaneous alignment identities for both fillings.

```lean
theorem overlayHyperplanes_spec (D E : GridFilling) :
    ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
        Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
      π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E) =
        (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E)
          (D.overlayHyperplanes E)).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion
```
