# Common Overlay rectangle carrier subset

Each closed rectangle with nonzero overlay coefficient lies in the closure of the
multiplicity-difference support.

```lean
theorem commonOverlay_rectangle_carrier_subset (D E : GridFilling)
    {I : BoxIntegral.Box (Fin 2)} (hI : I ∈ (D.commonOverlay E).support) :
    (rectangleOfBox I).carrier ⊆ closure (D.multiplicityDifferenceSupport E)
```
