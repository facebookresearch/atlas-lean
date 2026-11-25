# Grid Cells Meeting finite

At positive scale, only finitely many closed cells meet a bounded planar set.

```lean
theorem gridCellsMeeting_finite {S : Set ℂ} (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) : (gridCellsMeeting t S).Finite
```
