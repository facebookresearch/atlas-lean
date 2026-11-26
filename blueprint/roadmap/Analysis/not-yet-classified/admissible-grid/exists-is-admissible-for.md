# Exists is Admissible For

Every compact subset of an open planar set admits a finite positively oriented admissible grid
contour.

```lean
theorem exists_isAdmissibleFor {K G : Set ℂ} (hK : IsCompact K)
    (hG : IsOpen G) (hKG : K ⊆ G) : ∃ D : GridFilling, D.IsAdmissibleFor K G
```
