# Index of cell eq one of mem cell Interior

A counterclockwise cell boundary has analytic index one at an interior point.

```lean
theorem index_of_cell_eq_one_of_mem_cellInterior (D : GridFilling)
    (v : GridIndex) {z : ℂ} (hz : z ∈ D.cellInterior v) :
    (RectilinearCycle.ofRectangle (D.cell v)).index z = 1
```
