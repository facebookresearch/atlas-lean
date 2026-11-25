# Radius Set subset Icc

Every selected radius lies in the closed interval `[0,1]`.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem radiusSet_subset_Icc : E.radiusSet ⊆ Set.Icc 0 1
```
