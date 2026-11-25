# Mono left

Admissibility for an index-one set implies admissibility for each subset of that set.

```lean
theorem IsAdmissibleFor.mono_left {D : GridFilling} {K L G : Set ℂ}
    (hD : D.IsAdmissibleFor L G) (hKL : K ⊆ L) :
    D.IsAdmissibleFor K G
```
