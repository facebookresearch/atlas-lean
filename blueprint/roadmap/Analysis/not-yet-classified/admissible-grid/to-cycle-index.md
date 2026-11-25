# To Cycle index

The filling-cycle analytic index is the sum of the selected cells' analytic indices.

```lean
theorem toCycle_index (D : GridFilling) (z : ℂ) :
    D.toCycle.index z =
      ∑ v ∈ D.cells, (RectilinearCycle.ofRectangle (D.cell v)).index z
```
