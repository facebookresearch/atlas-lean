# Mem radius Set

Radius-set membership means membership in at least one of the finite closed intervals.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_radiusSet {r : ℝ} :
    r ∈ E.radiusSet ↔ ∃ i, r ∈ Set.Icc (E.inner i) (E.outer i)
```
