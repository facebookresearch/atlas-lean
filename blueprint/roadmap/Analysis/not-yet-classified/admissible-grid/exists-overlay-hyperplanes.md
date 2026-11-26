# Exists overlay Hyperplanes

Finitely many coordinate cuts align both cell prepartitions as restrictions of one global split.

```lean
theorem exists_overlayHyperplanes (D E : GridFilling) :
    ∃ s : Finset (Fin 2 × ℝ),
      ∀ π ∈ ({D.leftCellPrepartition E, D.rightCellPrepartition E} :
          Set (BoxIntegral.Prepartition (D.commonBoundingBox E))),
        π ⊓ BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s =
          (BoxIntegral.Prepartition.splitMany (D.commonBoundingBox E) s).filter
            fun J ↦ (J : Set (Fin 2 → ℝ)) ⊆ π.iUnion
```
