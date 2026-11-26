# Closure multiplicity Difference Support subset

Only points of the two reduced traces can be added by closing the multiplicity-difference
support.

```lean
theorem closure_multiplicityDifferenceSupport_subset (D E : GridFilling) :
    closure (D.multiplicityDifferenceSupport E) ⊆
      (D.multiplicityDifferenceSupport E ∪ D.reducedTrace) ∪ E.reducedTrace
```
