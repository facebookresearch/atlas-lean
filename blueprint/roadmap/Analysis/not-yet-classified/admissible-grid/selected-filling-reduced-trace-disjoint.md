# Selected Filling reduced Trace disjoint

The selected filling's reduced trace is disjoint from the original compact set.

```lean
theorem selectedFilling_reducedTrace_disjoint
    (K : Set ℂ) {r t : ℝ} (ht : 0 < t) (hK : IsCompact K) :
    Disjoint (selectedFilling K r t ht hK).reducedTrace K
```
