# Slit Domain subset ball

The slit domain lies in the open unit disk.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitDomain_subset_ball : E.slitDomain ⊆ Metric.ball 0 1
```
