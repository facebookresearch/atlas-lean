# Cell Multiplicity eq one iff overlay Box subset right

On an overlay box, second-filling multiplicity is one exactly when the whole box lies in the
second selected-cell union.

```lean
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_right
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    E.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.rightCellPrepartition E).iUnion
```
