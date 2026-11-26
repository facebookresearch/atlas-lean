# Mem multiplicity Difference Support of mem closure of not mem reduced Trace

Off both reduced traces, closure membership in the multiplicity-difference support implies
support membership.

```lean
theorem mem_multiplicityDifferenceSupport_of_mem_closure_of_not_mem_reducedTrace
    (D E : GridFilling) {z : ℂ}
    (hz : z ∈ closure (D.multiplicityDifferenceSupport E))
    (hzD : z ∉ D.reducedTrace) (hzE : z ∉ E.reducedTrace) :
    z ∈ D.multiplicityDifferenceSupport E
```
