# Reduced Trace subset region

The reduced trace lies in the selected closed-cell region.

```lean
theorem reducedTrace_subset_region (D : GridFilling) :
    D.reducedTrace ⊆ D.region
```
