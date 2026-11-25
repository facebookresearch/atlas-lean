# Complete Space

The analytic-representative submodule on an open domain is complete with the same inherited
restricted-volume L2 norm.

```lean
theorem completeSpace (G : Set ℂ) (hG : IsOpen G) :
    CompleteSpace (submodule G (volume.restrict G))
```
