# Mem owner cell carrier

Every complex point lies in its floor-based owner cell's closed carrier.

```lean
theorem mem_owner_cell_carrier (D : GridFilling) (z : ℂ) :
    z ∈ (D.cell (D.ownerIndex z)).carrier
```
