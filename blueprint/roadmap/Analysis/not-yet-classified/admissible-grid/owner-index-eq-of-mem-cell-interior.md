# Owner Index eq of mem cell Interior

A point in a cell's open interior has that cell as its owner.

```lean
theorem ownerIndex_eq_of_mem_cellInterior (D : GridFilling) {v : GridIndex}
    {z : ℂ} (hz : z ∈ D.cellInterior v) : D.ownerIndex z = v
```
