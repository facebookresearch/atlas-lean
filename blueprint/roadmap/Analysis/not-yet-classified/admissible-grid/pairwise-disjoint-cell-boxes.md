# Pairwise Disjoint cell Boxes

The finite selected half-open cell boxes are pairwise disjoint.

```lean
theorem pairwiseDisjoint_cellBoxes (D : GridFilling) :
    Set.Pairwise (↑D.cellBoxes)
      (Function.onFun Disjoint fun I : BoxIntegral.Box (Fin 2) ↦
        (I : Set (Fin 2 → ℝ)))
```
