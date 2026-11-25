# Common Overlay apply eq cell Multiplicity sub

The coefficient of an overlay box is the first multiplicity minus the second at any point of
that box.

```lean
theorem commonOverlay_apply_eq_cellMultiplicity_sub
    (D E : GridFilling) {I : BoxIntegral.Box (Fin 2)}
    (hI : I ∈ D.overlayPrepartition E) {z : ℂ}
    (hz : complexBoxPoint z ∈ I) :
    D.commonOverlay E I = D.cellMultiplicity z - E.cellMultiplicity z
```
