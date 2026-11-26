# Mem multiplicity Difference Support iff

Membership in the difference support means exactly that the two cell multiplicities differ.

```lean
theorem mem_multiplicityDifferenceSupport_iff (D E : GridFilling) (z : ℂ) :
    z ∈ D.multiplicityDifferenceSupport E ↔
      D.cellMultiplicity z ≠ E.cellMultiplicity z
```
