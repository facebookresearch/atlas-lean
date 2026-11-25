# Cell Box le common Bounding Box right

Each selected cell of the second filling lies in the nondegenerate common bounding box.

```lean
theorem cellBox_le_commonBoundingBox_right (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ E.cells) : E.cellBox v ≤ D.commonBoundingBox E
```
