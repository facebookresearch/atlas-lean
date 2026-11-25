# Exists is Admissible For with region subset

A compact set contained in an open planar set admits an admissible finite filling whose whole
cell region remains in the open set.

```lean
theorem exists_isAdmissibleFor_with_region_subset {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D : GridFilling, D.IsAdmissibleFor K G ∧ D.region ⊆ G
```
