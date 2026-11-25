# Cell Multiplicity eq one iff overlay Box subset left

On an overlay box, first-filling multiplicity is one exactly when the whole box lies in the
first selected-cell union.

```lean
theorem cellMultiplicity_eq_one_iff_overlayBox_subset_left
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.cellMultiplicity z = 1 ↔
      (I : Set (Fin 2 → ℝ)) ⊆ (D.leftCellPrepartition E).iUnion
```
