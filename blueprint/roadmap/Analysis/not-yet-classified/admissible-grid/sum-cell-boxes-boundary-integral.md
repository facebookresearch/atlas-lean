# Sum cell Boxes boundary Integral

The box-presentation boundary sum equals the boundary sum indexed by the selected grid cells.

```lean
theorem sum_cellBoxes_boundaryIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : GridFilling) (f : ℂ → E) :
    ∑ I ∈ D.cellBoxes, (rectangleOfBox I).boundaryIntegral f =
      ∑ v ∈ D.cells, (D.cell v).boundaryIntegral f
```
