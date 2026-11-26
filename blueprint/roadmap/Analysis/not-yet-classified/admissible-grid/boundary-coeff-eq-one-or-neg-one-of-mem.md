# Boundary Coeff eq one or neg one of mem

Every surviving boundary edge has coefficient one or negative one.

```lean
theorem boundaryCoeff_eq_one_or_neg_one_of_mem
    (D : GridFilling) {e : GridEdge} (he : e ∈ D.boundaryEdges) :
    D.boundaryCoeff e = 1 ∨ D.boundaryCoeff e = -1
```
