# Complex Box Point mem cells Prepartition i Union iff

A point belongs to the selected half-open prepartition union exactly when its multiplicity is
one.

```lean
theorem complexBoxPoint_mem_cellsPrepartition_iUnion_iff
    (D : GridFilling) (B : BoxIntegral.Box (Fin 2))
    (hB : ∀ v ∈ D.cells, D.cellBox v ≤ B) (z : ℂ) :
    complexBoxPoint z ∈ (D.cellsPrepartition B hB).iUnion ↔
      D.cellMultiplicity z = 1
```
