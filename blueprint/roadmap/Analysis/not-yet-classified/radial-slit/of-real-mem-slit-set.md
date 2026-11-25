# Of Real mem slit Set

A real-axis point lies on the slit exactly when its real coordinate belongs to the radius set.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem ofReal_mem_slitSet {r : ℝ} :
    (r : ℂ) ∈ E.slitSet ↔ r ∈ E.radiusSet
```
