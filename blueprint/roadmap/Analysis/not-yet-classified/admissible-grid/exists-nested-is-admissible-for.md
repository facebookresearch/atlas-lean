# Exists nested is Admissible For

Nested admissible grids for the classical multiplicativity argument.  The
outer grid has index one on the entire inner grid region and its reduced
trace is strictly outside that region.  By `IsAdmissibleFor.mono_left` it is
also admissible for the original compact set.

```lean
theorem exists_nested_isAdmissibleFor {K G : Set ℂ}
    (hK : IsCompact K) (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ D E : GridFilling,
      D.IsAdmissibleFor K G ∧ E.IsAdmissibleFor (K ∪ D.region) G
```
