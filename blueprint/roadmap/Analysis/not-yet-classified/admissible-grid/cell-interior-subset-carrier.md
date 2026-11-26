# Cell Interior subset carrier

A cell's open interior lies in its closed carrier.

```lean
theorem cellInterior_subset_carrier (D : GridFilling) (v : GridIndex) :
    D.cellInterior v ⊆ (D.cell v).carrier
```
