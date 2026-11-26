# Mem closure cell Interior owner Index

Every complex point lies in the closure of its owner cell's open interior.

```lean
theorem mem_closure_cellInterior_ownerIndex (D : GridFilling) (z : ℂ) :
    z ∈ closure (D.cellInterior (D.ownerIndex z))
```
