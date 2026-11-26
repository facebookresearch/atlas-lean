# Continuous At to Cycle index of not mem reduced Trace

The filling's analytic winding index is continuous off its reduced boundary.

```lean
theorem continuousAt_toCycle_index_of_not_mem_reducedTrace
    (D : GridFilling) {z : ℂ} (hz : z ∉ D.reducedTrace) :
    ContinuousAt (fun w : ℂ ↦ D.toCycle.index w) z
```
