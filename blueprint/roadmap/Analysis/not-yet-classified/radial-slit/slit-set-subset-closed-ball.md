# Slit Set subset closed Ball

The slit lies in the closed unit disk.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitSet_subset_closedBall : E.slitSet ⊆ Metric.closedBall 0 1
```
