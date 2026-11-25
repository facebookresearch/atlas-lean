# Submodule is Closed

The analytic-representative submodule is closed in scalar L2 of planar volume restricted to an
open domain.

```lean
theorem submodule_isClosed (G : Set ℂ) (hG : IsOpen G) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G)))
```
