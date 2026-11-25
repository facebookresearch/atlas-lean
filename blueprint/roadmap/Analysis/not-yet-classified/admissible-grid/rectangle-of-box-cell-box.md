# Rectangle Of Box cell Box

The half-open presentation of a cell has exactly the same associated closed rectangle.

```lean
theorem rectangleOfBox_cellBox (D : GridFilling) (v : GridIndex) :
    rectangleOfBox (D.cellBox v) = D.cell v
```
