# Disjoint cell Box

Distinct half-open grid cells are disjoint, with boundary faces assigned by the half-open
convention.

```lean
theorem disjoint_cellBox (D : GridFilling) {v w : GridIndex} (hvw : v ≠ w) :
    Disjoint (D.cellBox v : Set (Fin 2 → ℝ)) (D.cellBox w : Set (Fin 2 → ℝ))
```
