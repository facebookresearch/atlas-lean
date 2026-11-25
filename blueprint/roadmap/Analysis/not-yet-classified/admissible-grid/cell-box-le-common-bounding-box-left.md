# Cell Box le common Bounding Box left

Each selected cell of the first filling lies in the nondegenerate common bounding box.

```lean
theorem cellBox_le_commonBoundingBox_left (D E : GridFilling)
    {v : GridIndex} (hv : v ∈ D.cells) : D.cellBox v ≤ D.commonBoundingBox E
```
